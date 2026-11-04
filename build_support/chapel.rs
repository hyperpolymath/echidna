// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! Native Linux link contract for the optional Chapel bridge.
//!
//! The bridge archive does not contain the Chapel runtime. Real mode obtains
//! its dependency closure from the installed compiler's official compileline
//! helper; unsupported flags and failed tools are errors, never empty success.

use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Stubs,
    Real,
}

pub fn parse_mode(value: &str) -> Result<Mode, String> {
    match value {
        "stubs" | "stubs\n" => Ok(Mode::Stubs),
        "real" | "real\n" => Ok(Mode::Real),
        _ => Err("unknown Chapel artifact mode; rebuild the Zig bridge".into()),
    }
}

fn require_mode(actual: Mode, expected: Option<&str>) -> Result<(), String> {
    if let Some(expected) = expected {
        if actual != parse_mode(expected)? {
            return Err("Chapel artifact mode differs from ECHIDNA_CHAPEL_EXPECT_MODE".into());
        }
    }
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
pub enum LinkFlag {
    Search(String),
    Library(String),
    Rpath(String),
}

pub fn parse_runtime_flags(output: &str) -> Result<Vec<LinkFlag>, String> {
    let output = output.trim();
    if output.is_empty()
        || output
            .chars()
            .any(|c| matches!(c, '\n' | '\r' | '\0' | '\'' | '"' | '\\'))
    {
        return Err("empty, multiline, or quoted Chapel runtime flags are unsupported".into());
    }

    let mut flags = Vec::new();
    let mut has_runtime = false;
    for flag in output.split_ascii_whitespace() {
        if let Some(path) = flag.strip_prefix("-L") {
            if !Path::new(path).is_absolute() {
                return Err(format!(
                    "Chapel library search path must be absolute: {flag}"
                ));
            }
            flags.push(LinkFlag::Search(path.into()));
        } else if let Some(name) = flag.strip_prefix("-l") {
            if name.is_empty()
                || !name
                    .bytes()
                    .all(|c| c.is_ascii_alphanumeric() || b"_+.-".contains(&c))
            {
                return Err(format!("unsupported Chapel library name: {flag}"));
            }
            has_runtime |= name == "chpl";
            flags.push(LinkFlag::Library(name.into()));
        } else if let Some(path) = flag.strip_prefix("-Wl,-rpath,") {
            if !Path::new(path).is_absolute() {
                return Err(format!("Chapel runtime rpath must be absolute: {flag}"));
            }
            flags.push(LinkFlag::Rpath(flag.into()));
        } else {
            return Err(format!("unsupported Chapel runtime link flag: {flag}"));
        }
    }
    if !has_runtime || !flags.iter().any(|flag| matches!(flag, LinkFlag::Search(_))) {
        return Err("Chapel compileline omitted its runtime library or search directory".into());
    }
    Ok(flags)
}

/// The installed compiler owns these paths; prefix installs do not keep their
/// runtime and third-party files beneath CHPL_HOME.
#[derive(Debug, PartialEq, Eq)]
struct CompilerLayout {
    home: PathBuf,
    runtime_lib: PathBuf,
    runtime_incl: PathBuf,
    third_party: PathBuf,
}

fn layout_path(line: Option<&str>, key: &str) -> Result<PathBuf, String> {
    let prefix = format!("{key}: ");
    let value = line
        .and_then(|line| line.strip_prefix(prefix.as_str()))
        .ok_or_else(|| format!("compiler settings omitted or reordered {key}"))?;
    if !Path::new(value).is_absolute() || value.chars().any(char::is_control) {
        return Err(format!(
            "compiler setting {key} is not an absolute ordinary path"
        ));
    }
    Ok(PathBuf::from(value))
}

fn parse_compiler_layout(output: &str) -> Result<CompilerLayout, String> {
    // Chapel 2.8 prints this ordered header, then a blank line and printchplenv.
    // The later human-readable settings repeat CHPL_HOME with origin markers.
    let mut lines = output.lines();
    let layout = CompilerLayout {
        home: layout_path(lines.next(), "CHPL_HOME")?,
        runtime_lib: layout_path(lines.next(), "CHPL_RUNTIME_LIB")?,
        runtime_incl: layout_path(lines.next(), "CHPL_RUNTIME_INCL")?,
        third_party: layout_path(lines.next(), "CHPL_THIRD_PARTY")?,
    };
    if lines.next() != Some("") {
        return Err("compiler settings header has no blank separator".into());
    }
    Ok(layout)
}

fn compiler_runtime_flags(layout: &CompilerLayout) -> Result<Vec<LinkFlag>, String> {
    let environment = [
        ("CHPL_HOME", layout.home.as_path()),
        ("CHPL_RUNTIME_LIB", layout.runtime_lib.as_path()),
        ("CHPL_RUNTIME_INCL", layout.runtime_incl.as_path()),
        ("CHPL_THIRD_PARTY", layout.third_party.as_path()),
    ];
    for (key, path) in &environment {
        if !path.is_dir() {
            return Err(format!("compiler-selected {key} directory is unavailable"));
        }
    }
    let compileline = layout.home.join("util/config/compileline");
    println!("cargo:rerun-if-changed={}", display_path(&compileline)?);
    let output = command_text_with_env(&compileline, &["--libraries"], &environment)?;
    parse_runtime_flags(&output)
}

fn command_text(program: &Path, arguments: &[&str]) -> Result<String, String> {
    command_text_with_env(program, arguments, &[])
}

fn command_text_with_env(
    program: &Path,
    arguments: &[&str],
    environment: &[(&str, &Path)],
) -> Result<String, String> {
    let output = Command::new(program)
        .args(arguments)
        .envs(environment.iter().copied())
        .output()
        .map_err(|error| format!("cannot execute {}: {error}", program.display()))?;
    if !output.status.success() {
        return Err(format!(
            "{} failed with {}: {}",
            program.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let value = String::from_utf8(output.stdout)
        .map_err(|_| format!("{} returned non-UTF-8 output", program.display()))?;
    if value.trim().is_empty() {
        return Err(format!("{} returned no output", program.display()));
    }
    Ok(value)
}

fn display_path(path: &Path) -> Result<&str, String> {
    let value = path.to_str().ok_or("Chapel path is not UTF-8")?;
    if value.chars().any(|c| matches!(c, '\n' | '\r' | '\0')) {
        return Err("Chapel path contains a line separator".into());
    }
    Ok(value)
}

pub fn configure(root: &Path) -> Result<(), String> {
    for variable in [
        "ECHIDNA_CHAPEL_EXPECT_MODE",
        "ECHIDNA_CHAPEL_LIB_DIR",
        "PATH",
        "CHPL_HOME",
        "CHPL_RUNTIME_LIB",
        "CHPL_RUNTIME_INCL",
        "CHPL_THIRD_PARTY",
        "CHPL_TARGET_COMPILER",
        "CHPL_TARGET_CPU",
        "CHPL_COMM",
        "CHPL_TASKS",
        "CHPL_LOCALE_MODEL",
        "CHPL_LIB_PIC",
        "CHPL_MEM",
        "CHPL_GMP",
        "CHPL_HWLOC",
        "CHPL_RE2",
        "CHPL_UNWIND",
    ] {
        println!("cargo:rerun-if-env-changed={variable}");
    }

    let expected = match std::env::var("ECHIDNA_CHAPEL_EXPECT_MODE") {
        Ok(value) => Some(value),
        Err(std::env::VarError::NotPresent) => None,
        Err(error) => return Err(format!("invalid requested Chapel mode: {error}")),
    };
    if let Some(expected) = expected.as_deref() {
        parse_mode(expected)?;
    }

    let candidates = [root.join("src/zig_ffi/zig-out/lib"), root.join("lib")];
    for path in &candidates {
        println!("cargo:rerun-if-changed={}", display_path(path)?);
        for filename in ["libechidna_chapel_ffi.a", "echidna_chapel_ffi.mode"] {
            println!(
                "cargo:rerun-if-changed={}",
                display_path(&path.join(filename))?
            );
        }
    }

    let bridge = match candidates
        .iter()
        .find(|path| path.join("libechidna_chapel_ffi.a").is_file())
    {
        Some(path) => path,
        None if expected.is_none() => {
            // Keep metadata-only cargo check/clippy usable without optional SDKs.
            // A linked binary still cannot succeed without the bridge symbols.
            println!("cargo:warning=Chapel bridge absent; build with just build-chapel-ffi");
            return Ok(());
        },
        None => return Err("requested Chapel mode has no bridge archive".into()),
    };

    let mode_path = bridge.join("echidna_chapel_ffi.mode");
    let mode_text = std::fs::read_to_string(&mode_path).map_err(|error| {
        format!(
            "read {}: {error}; rebuild the Zig bridge",
            mode_path.display()
        )
    })?;
    let mode = parse_mode(&mode_text)?;
    require_mode(mode, expected.as_deref())?;

    println!("cargo:rustc-link-search=native={}", display_path(bridge)?);
    println!("cargo:rustc-link-lib=static=echidna_chapel_ffi");
    println!("cargo:rustc-link-lib=dylib=c");
    if mode == Mode::Stubs {
        println!("cargo:rustc-cfg=echidna_chapel_stubs");
        return Ok(());
    }

    let host = std::env::var("HOST").map_err(|error| format!("Cargo HOST unavailable: {error}"))?;
    let target =
        std::env::var("TARGET").map_err(|error| format!("Cargo TARGET unavailable: {error}"))?;
    if host != target || std::env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux") {
        return Err("real Chapel linkage currently requires a native Linux target".into());
    }

    let library_dir = std::env::var_os("ECHIDNA_CHAPEL_LIB_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("src/chapel/lib"))
        .canonicalize()
        .map_err(|error| format!("real Chapel library directory is unavailable: {error}"))?;
    let archive = library_dir.join("libechidna_chapel.a");
    if !archive.is_file() {
        return Err(format!(
            "missing real Chapel archive: {}",
            archive.display()
        ));
    }
    println!("cargo:rerun-if-changed={}", display_path(&archive)?);

    let settings = command_text(Path::new("chpl"), &["--print-chpl-settings"])?;
    let layout = parse_compiler_layout(&settings)?;
    let flags = compiler_runtime_flags(&layout)?;
    let runtime_exists = flags.iter().any(|flag| match flag {
        LinkFlag::Search(path) => Path::new(path).join("libchpl.a").is_file(),
        _ => false,
    });
    if !runtime_exists {
        return Err("compiler-selected static libchpl.a is unavailable".into());
    }

    println!(
        "cargo:rustc-link-search=native={}",
        display_path(&library_dir)?
    );
    println!("cargo:rustc-link-lib=static=echidna_chapel");
    for flag in flags {
        match flag {
            LinkFlag::Search(path) => {
                println!("cargo:rerun-if-changed={path}");
                println!("cargo:rustc-link-search=native={path}");
            },
            LinkFlag::Library(name) if name == "chpl" => {
                println!("cargo:rustc-link-lib=static=chpl");
            },
            LinkFlag::Library(name) => println!("cargo:rustc-link-lib={name}"),
            LinkFlag::Rpath(flag) => println!("cargo:rustc-link-arg={flag}"),
        }
    }
    println!("cargo:rustc-cfg=echidna_chapel_real");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const PREFIX_SETTINGS: &str = concat!(
        "CHPL_HOME: /prefix/share/chapel/2.8\n",
        "CHPL_RUNTIME_LIB: /prefix/lib/chapel/2.8/runtime/lib\n",
        "CHPL_RUNTIME_INCL: /prefix/lib/chapel/2.8/runtime/include\n",
        "CHPL_THIRD_PARTY: /prefix/lib/chapel/2.8/third-party\n",
        "\n",
        "machine info: fixture\n",
        "CHPL_HOME: /prefix/share/chapel/2.8 *\n",
    );

    #[test]
    fn installed_layout_comes_from_the_compiler_header() {
        let layout = parse_compiler_layout(PREFIX_SETTINGS).unwrap();
        assert_eq!(layout.home, Path::new("/prefix/share/chapel/2.8"));
        assert_eq!(
            layout.runtime_lib,
            Path::new("/prefix/lib/chapel/2.8/runtime/lib")
        );
        assert_eq!(
            layout.runtime_incl,
            Path::new("/prefix/lib/chapel/2.8/runtime/include")
        );
        assert_eq!(
            layout.third_party,
            Path::new("/prefix/lib/chapel/2.8/third-party")
        );
    }

    #[test]
    fn compiler_layout_rejects_incomplete_ambiguous_and_relative_headers() {
        let invalid = [
            String::new(),
            PREFIX_SETTINGS.replace("CHPL_RUNTIME_LIB: /prefix/lib/chapel/2.8/runtime/lib\n", ""),
            PREFIX_SETTINGS.replace(
                "CHPL_RUNTIME_LIB: /prefix/lib/chapel/2.8/runtime/lib",
                "CHPL_RUNTIME_LIB: relative/lib",
            ),
            PREFIX_SETTINGS.replace("CHPL_RUNTIME_INCL:", "CHPL_RUNTIME_LIB:"),
            format!("CHPL_HOME: /different\n{PREFIX_SETTINGS}"),
            PREFIX_SETTINGS.replace("\n\n", "\nCHPL_HOME: /different\n\n"),
            PREFIX_SETTINGS.replace("\n\n", "\n"),
            PREFIX_SETTINGS.replace("/prefix/lib/chapel/2.8/third-party", ""),
            PREFIX_SETTINGS.replace("/prefix/lib/chapel/2.8/third-party", "/bad\0path"),
            PREFIX_SETTINGS.replace("/prefix/lib/chapel/2.8/third-party", "/bad\tpath"),
        ];
        for output in invalid {
            assert!(parse_compiler_layout(&output).is_err(), "{output:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn actual_helper_receives_every_compiler_selected_directory() {
        use std::os::unix::fs::PermissionsExt;
        use std::time::{SystemTime, UNIX_EPOCH};

        struct TemporaryDirectory(PathBuf);
        impl Drop for TemporaryDirectory {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }

        let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
        let root = std::env::temp_dir().join(format!(
            "echidna-chapel-layout-{}-{}",
            std::process::id(),
            unique.as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let _cleanup = TemporaryDirectory(root.clone());
        let layout = CompilerLayout {
            home: root.join("home"),
            runtime_lib: root.join("runtime-lib"),
            runtime_incl: root.join("runtime-include"),
            third_party: root.join("third-party"),
        };
        for path in [
            &layout.home,
            &layout.runtime_lib,
            &layout.runtime_incl,
            &layout.third_party,
        ] {
            std::fs::create_dir(path).unwrap();
        }
        std::fs::create_dir_all(layout.home.join("util/config")).unwrap();
        let helper = layout.home.join("util/config/compileline");
        let script = concat!(
            "#!/bin/sh\n",
            "[ \"$#\" -eq 1 ] && [ \"$1\" = --libraries ] || exit 9\n",
            "printf '%s\\n' \"-L$CHPL_RUNTIME_LIB -lchpl ",
            "-L$CHPL_RUNTIME_INCL -L$CHPL_THIRD_PARTY -L$CHPL_HOME\"\n",
        );
        std::fs::write(&helper, script).unwrap();
        std::fs::set_permissions(&helper, std::fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(
            compiler_runtime_flags(&layout).unwrap(),
            vec![
                LinkFlag::Search(layout.runtime_lib.to_str().unwrap().into()),
                LinkFlag::Library("chpl".into()),
                LinkFlag::Search(layout.runtime_incl.to_str().unwrap().into()),
                LinkFlag::Search(layout.third_party.to_str().unwrap().into()),
                LinkFlag::Search(layout.home.to_str().unwrap().into()),
            ]
        );

        for failed_script in [
            "#!/bin/sh\nprintf '%s\\n' '-L/valid-looking -lchpl'; exit 2\n",
            "#!/bin/sh\nexit 0\n",
        ] {
            std::fs::write(&helper, failed_script).unwrap();
            assert!(compiler_runtime_flags(&layout).is_err());
        }
        std::fs::remove_file(&helper).unwrap();
        assert!(compiler_runtime_flags(&layout).is_err());
    }

    #[test]
    fn separates_real_and_stub_modes() {
        assert_eq!(parse_mode("real\n"), Ok(Mode::Real));
        assert_eq!(parse_mode("stubs\n"), Ok(Mode::Stubs));
        assert!(require_mode(Mode::Real, Some("real")).is_ok());
        assert!(require_mode(Mode::Stubs, Some("real")).is_err());
        assert!(require_mode(Mode::Real, Some("stubs")).is_err());
        for invalid in ["", "REAL", "real\nstubs", " real", "stub"] {
            assert!(parse_mode(invalid).is_err(), "{invalid:?}");
        }
    }

    #[test]
    fn retains_compiler_library_order_and_paths() {
        assert_eq!(
            parse_runtime_flags(
                "-L/opt/chapel/lib -lchpl -L/opt/qthread/lib -lqthread -lm -lpthread -ldl\n"
            ),
            Ok(vec![
                LinkFlag::Search("/opt/chapel/lib".into()),
                LinkFlag::Library("chpl".into()),
                LinkFlag::Search("/opt/qthread/lib".into()),
                LinkFlag::Library("qthread".into()),
                LinkFlag::Library("m".into()),
                LinkFlag::Library("pthread".into()),
                LinkFlag::Library("dl".into()),
            ])
        );
    }

    #[test]
    fn accepts_an_absolute_runtime_rpath_without_dropping_it() {
        let flags = parse_runtime_flags("-L/opt/lib -lchpl -Wl,-rpath,/opt/lib").unwrap();
        assert_eq!(
            flags.last(),
            Some(&LinkFlag::Rpath("-Wl,-rpath,/opt/lib".into()))
        );
    }

    #[test]
    fn refuses_missing_runtime_unknown_flags_and_ambiguous_paths() {
        for invalid in [
            "",
            "-L/opt/lib -lm",
            "-lchpl",
            "-Lrelative -lchpl",
            "-L/opt/lib -lchpl -unknown",
            "-L'/path with spaces' -lchpl",
            "-L/opt/lib -lchpl\n-lm",
            "-L/opt/lib -lchpl -Wl,--start-group",
            "-L/opt/lib -lchpl -Wl,-rpath,relative",
            "-L/opt/lib -lchpl -l",
        ] {
            assert!(parse_runtime_flags(invalid).is_err(), "{invalid:?}");
        }
    }

    #[test]
    fn actual_tool_failure_cannot_promote_valid_looking_stdout() {
        let shell = Path::new("sh");
        assert!(
            command_text(shell, &["-c", "printf '%s\\n' '-L/opt/lib -lchpl'; exit 2"]).is_err()
        );
        assert!(command_text(shell, &["-c", "exit 0"]).is_err());
        assert!(command_text(Path::new("/definitely-missing-chapel-tool"), &[]).is_err());
        let output = command_text(shell, &["-c", "printf '%s\\n' '-L/opt/lib -lchpl'"]).unwrap();
        assert!(parse_runtime_flags(&output).is_ok());
    }
}
