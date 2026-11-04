// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell
//
// A single OS thread owns a native runtime from initialization to finalization.
// Work is synchronous: the caller retains its context until call() completes.
const std = @import("std");

pub const Work = struct {
    context: *anyopaque,
    run: *const fn (*anyopaque) void,
    completed: bool = false,
};

pub const CallError = error{ RuntimeUnavailable, ReentrantCall, RuntimeBusy };

pub fn Owner(comptime Runtime: type) type {
    return struct {
        const Self = @This();
        const State = enum { idle, running, exit_refused, stopping, stopped, failed };

        runtime: Runtime,
        mutex: std.Thread.Mutex = .{},
        work_available: std.Thread.Condition = .{},
        changed: std.Thread.Condition = .{},
        state: State = .idle,
        worker: ?std.Thread = null,
        worker_id: ?std.Thread.Id = null,
        pending: ?*Work = null,

        pub fn init(runtime: Runtime) Self {
            return .{ .runtime = runtime };
        }

        // No context or native result escapes the completion handshake.
        // Re-entry from a native callback is refused, not queued behind itself.
        pub fn call(self: *Self, work: *Work) CallError!void {
            self.mutex.lock();
            defer self.mutex.unlock();

            if (self.worker_id == std.Thread.getCurrentId()) return error.ReentrantCall;
            if (self.state == .idle) {
                self.state = .running;
                self.worker = std.Thread.spawn(.{}, run, .{self}) catch {
                    self.state = .failed;
                    return error.RuntimeUnavailable;
                };
            }

            while (self.pending != null and self.state == .running) {
                self.changed.wait(&self.mutex);
            }
            if (self.state != .running) return error.RuntimeUnavailable;

            work.completed = false;
            self.pending = work;
            self.work_available.signal();
            while (!work.completed) self.changed.wait(&self.mutex);
        }

        // Stop admission, finish the one accepted request, finalize on its
        // owner, and join. Concurrent shutdown callers wait for the same join.
        // An idle or closed owner is never restarted.
        pub fn shutdown(self: *Self) CallError!void {
            return self.stop(true);
        }

        // atexit can run on an unknown Chapel task which the owner is waiting
        // for. Joining active work there can deadlock. Close admission and
        // refuse instead; the exit handler must turn this refusal into abort.
        pub fn shutdownForProcessExit(self: *Self) CallError!void {
            return self.stop(false);
        }

        fn stop(self: *Self, allow_active: bool) CallError!void {
            self.mutex.lock();
            if (!allow_active and
                (self.pending != null or self.state == .stopping or self.state == .exit_refused))
            {
                if (self.state == .running) {
                    self.state = .exit_refused;
                    self.work_available.signal();
                    self.changed.broadcast();
                }
                self.mutex.unlock();
                return error.RuntimeBusy;
            }
            if (self.worker_id == std.Thread.getCurrentId()) {
                self.mutex.unlock();
                return error.ReentrantCall;
            }

            switch (self.state) {
                .idle, .failed => {
                    self.state = .stopped;
                    self.mutex.unlock();
                    return;
                },
                .stopped => {
                    self.mutex.unlock();
                    return;
                },
                .stopping => {
                    while (self.state != .stopped) self.changed.wait(&self.mutex);
                    self.mutex.unlock();
                    return;
                },
                .running, .exit_refused => {},
            }

            self.state = .stopping;
            self.work_available.signal();
            self.changed.broadcast();
            const worker = self.worker.?;
            self.mutex.unlock();

            worker.join();

            self.mutex.lock();
            self.worker = null;
            self.worker_id = null;
            self.state = .stopped;
            self.changed.broadcast();
            self.mutex.unlock();
        }

        fn run(self: *Self) void {
            self.mutex.lock();
            self.worker_id = std.Thread.getCurrentId();
            self.mutex.unlock();

            self.runtime.initialize();
            self.mutex.lock();
            while (true) {
                while (self.pending == null and self.state == .running) {
                    self.work_available.wait(&self.mutex);
                }
                const work = self.pending orelse break;
                self.mutex.unlock();

                work.run(work.context);

                self.mutex.lock();
                work.completed = true;
                self.pending = null;
                self.changed.broadcast();
            }
            self.mutex.unlock();
            self.runtime.finalize();
        }
    };
}

const Probe = struct {
    init_id: std.Thread.Id = 0,
    finalize_id: std.Thread.Id = 0,
    initialized: usize = 0,
    finalized: usize = 0,
    calls: usize = 0,
    wrong_thread: bool = false,

    fn initialize(self: *@This()) void {
        self.init_id = std.Thread.getCurrentId();
        self.initialized += 1;
    }

    fn finalize(self: *@This()) void {
        self.finalize_id = std.Thread.getCurrentId();
        self.finalized += 1;
    }

    fn work(raw: *anyopaque) void {
        const self: *@This() = @ptrCast(@alignCast(raw));
        self.wrong_thread = self.wrong_thread or self.init_id != std.Thread.getCurrentId();
        self.calls += 1;
    }
};

test "one OS thread owns init concurrent work and finalization" {
    const TestOwner = Owner(*Probe);
    var probe = Probe{};
    var owner = TestOwner.init(&probe);
    defer owner.shutdown() catch unreachable;

    const Caller = struct {
        owner: *TestOwner,
        probe: *Probe,
        failed: bool = false,
        id: std.Thread.Id = 0,

        fn run(self: *@This()) void {
            self.id = std.Thread.getCurrentId();
            var work = Work{ .context = self.probe, .run = Probe.work };
            for (0..2) |_| self.owner.call(&work) catch {
                self.failed = true;
                return;
            };
        }
    };
    var callers: [4]Caller = undefined;
    var threads: [4]std.Thread = undefined;
    var started: usize = 0;
    defer for (threads[0..started]) |thread| thread.join();
    for (&callers, &threads) |*caller, *thread| {
        caller.* = .{ .owner = &owner, .probe = &probe };
        thread.* = try std.Thread.spawn(.{}, Caller.run, .{caller});
        started += 1;
    }
    for (threads[0..started]) |thread| thread.join();
    started = 0;
    try owner.shutdownForProcessExit();

    try std.testing.expectEqual(@as(usize, 1), probe.initialized);
    try std.testing.expectEqual(@as(usize, 1), probe.finalized);
    try std.testing.expectEqual(@as(usize, 8), probe.calls);
    try std.testing.expectEqual(probe.init_id, probe.finalize_id);
    try std.testing.expect(!probe.wrong_thread);
    for (callers) |caller| {
        try std.testing.expect(!caller.failed);
        try std.testing.expect(caller.id != probe.init_id);
    }
    var refused = Work{ .context = &probe, .run = Probe.work };
    try std.testing.expectError(error.RuntimeUnavailable, owner.call(&refused));
    try std.testing.expectEqual(@as(usize, 8), probe.calls);
}

test "shutdown drains accepted work and refuses new work before joining" {
    const TestOwner = Owner(*Probe);
    var probe = Probe{};
    var owner = TestOwner.init(&probe);
    defer owner.shutdown() catch unreachable;

    const Blocked = struct {
        owner: *TestOwner,
        mutex: std.Thread.Mutex = .{},
        changed: std.Thread.Condition = .{},
        entered: bool = false,
        release: bool = false,
        call_failed: bool = false,
        shutdown_failed: bool = false,

        fn work(raw: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(raw));
            self.mutex.lock();
            self.entered = true;
            self.changed.broadcast();
            while (!self.release) self.changed.wait(&self.mutex);
            self.mutex.unlock();
        }

        fn call(self: *@This()) void {
            var request = Work{ .context = self, .run = work };
            self.owner.call(&request) catch {
                self.call_failed = true;
            };
        }

        fn stop(self: *@This()) void {
            self.owner.shutdown() catch {
                self.shutdown_failed = true;
            };
        }
    };
    var blocked = Blocked{ .owner = &owner };
    const caller = try std.Thread.spawn(.{}, Blocked.call, .{&blocked});
    var caller_joined = false;
    defer if (!caller_joined) caller.join();
    // Release the callback even if starting the shutdown thread fails.
    defer {
        blocked.mutex.lock();
        blocked.release = true;
        blocked.changed.broadcast();
        blocked.mutex.unlock();
    }

    blocked.mutex.lock();
    while (!blocked.entered) blocked.changed.wait(&blocked.mutex);
    blocked.mutex.unlock();

    const stopper = try std.Thread.spawn(.{}, Blocked.stop, .{&blocked});
    owner.mutex.lock();
    while (owner.state != .stopping) owner.changed.wait(&owner.mutex);
    owner.mutex.unlock();
    var refused = Work{ .context = &probe, .run = Probe.work };
    const rejected = if (owner.call(&refused)) |_| false else |err| err == error.RuntimeUnavailable;

    blocked.mutex.lock();
    blocked.release = true;
    blocked.changed.broadcast();
    blocked.mutex.unlock();
    stopper.join();
    caller.join();
    caller_joined = true;
    // Both the submitter and owner have completed before inspecting results.
    try std.testing.expect(rejected);
    try std.testing.expect(!blocked.call_failed);
    try std.testing.expect(!blocked.shutdown_failed);
    try std.testing.expectEqual(@as(usize, 1), probe.finalized);
    try std.testing.expectEqual(probe.init_id, probe.finalize_id);
    try std.testing.expectEqual(@as(usize, 0), probe.calls);
}

test "owner callbacks cannot re-enter or finalize themselves" {
    const TestOwner = Owner(*Probe);
    var probe = Probe{};
    var owner = TestOwner.init(&probe);
    defer owner.shutdown() catch unreachable;
    const Callback = struct {
        owner: *TestOwner,
        probe: *Probe,
        call_refused: bool = false,
        stop_refused: bool = false,

        fn work(raw: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(raw));
            var nested = Work{ .context = self.probe, .run = Probe.work };
            self.call_refused = if (self.owner.call(&nested)) |_| false else |err| err == error.ReentrantCall;
            self.stop_refused = if (self.owner.shutdown()) |_| false else |err| err == error.ReentrantCall;
        }
    };
    var callback = Callback{ .owner = &owner, .probe = &probe };
    var request = Work{ .context = &callback, .run = Callback.work };
    try owner.call(&request);
    var following = Work{ .context = &probe, .run = Probe.work };
    try owner.call(&following);
    try owner.shutdown();

    try std.testing.expect(callback.call_refused and callback.stop_refused);
    try std.testing.expectEqual(@as(usize, 1), probe.calls);
    try std.testing.expectEqual(@as(usize, 1), probe.finalized);
}

test "shutdown before initialization never starts the runtime" {
    var probe = Probe{};
    var owner = Owner(*Probe).init(&probe);
    try owner.shutdown();
    try owner.shutdown();
    var request = Work{ .context = &probe, .run = Probe.work };
    try std.testing.expectError(error.RuntimeUnavailable, owner.call(&request));
    try std.testing.expectEqual(@as(usize, 0), probe.initialized);
    try std.testing.expectEqual(@as(usize, 0), probe.finalized);
}


test "a nonowner process-exit request refuses active work without a join cycle" {
    const TestOwner = Owner(*Probe);
    var probe = Probe{};
    var owner = TestOwner.init(&probe);
    defer owner.shutdown() catch unreachable;

    const Active = struct {
        owner: *TestOwner,
        mutex: std.Thread.Mutex = .{},
        changed: std.Thread.Condition = .{},
        entered: bool = false,
        release: bool = false,
        call_failed: bool = false,
        exit_done: bool = false,
        exit_refused: bool = false,

        fn work(raw: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(raw));
            self.mutex.lock();
            self.entered = true;
            self.changed.broadcast();
            while (!self.release) self.changed.wait(&self.mutex);
            self.mutex.unlock();
        }

        fn call(self: *@This()) void {
            var request = Work{ .context = self, .run = work };
            self.owner.call(&request) catch {
                self.call_failed = true;
            };
        }

        fn processExit(self: *@This()) void {
            const refused = if (self.owner.shutdownForProcessExit()) |_| false else |err| err == error.RuntimeBusy;
            self.mutex.lock();
            self.exit_refused = refused;
            self.exit_done = true;
            self.changed.broadcast();
            self.mutex.unlock();
        }
    };

    var active = Active{ .owner = &owner };
    const caller = try std.Thread.spawn(.{}, Active.call, .{&active});
    var caller_joined = false;
    defer if (!caller_joined) caller.join();
    defer {
        active.mutex.lock();
        active.release = true;
        active.changed.broadcast();
        active.mutex.unlock();
    }

    active.mutex.lock();
    while (!active.entered) active.changed.wait(&active.mutex);
    active.mutex.unlock();
    var timer = try std.time.Timer.start();
    const exit_thread = try std.Thread.spawn(.{}, Active.processExit, .{&active});
    active.mutex.lock();
    while (!active.exit_done) {
        const remaining = std.time.ns_per_s -| timer.read();
        if (remaining == 0) break;
        active.changed.timedWait(&active.mutex, remaining) catch break;
    }
    const promptly_refused = active.exit_done and active.exit_refused;
    // A regressed draining exit path can now finish too: the negative control
    // fails after cleanup, rather than leaving the test owner blocked forever.
    active.release = true;
    active.changed.broadcast();
    active.mutex.unlock();

    exit_thread.join();
    caller.join();
    caller_joined = true;
    var refused = Work{ .context = &probe, .run = Probe.work };
    const admission_closed = if (owner.call(&refused)) |_| false else |err| err == error.RuntimeUnavailable;
    try owner.shutdown();

    try std.testing.expect(promptly_refused);
    try std.testing.expect(admission_closed);
    try std.testing.expect(!active.call_failed);
    try std.testing.expectEqual(@as(usize, 0), probe.calls);
    try std.testing.expectEqual(@as(usize, 1), probe.finalized);
    try std.testing.expectEqual(probe.init_id, probe.finalize_id);
}
