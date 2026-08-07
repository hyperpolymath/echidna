// SPDX-License-Identifier: AGPL-3.0-or-later
// Echidna GUI Bridge

/**
 * Wraps the Echidna AffineScript Wasm module.
 */
class EchidnaTEA {
  constructor(exports) {
    this.exports = exports;
    this.memory = exports.memory;
  }

  init() {
    return this.exports.echidna_init();
  }

  update(msg, model) {
    return this.exports.echidna_update(msg, model);
  }

  view(model) {
    const ptr = this.exports.echidna_view(model);
    return this.readString(ptr);
  }

  subs(model) {
    const ptr = this.exports.echidna_subs(model);
    return this.readString(ptr);
  }

  readString(ptr) {
    const view = new DataView(this.memory.buffer);
    const len = view.getInt32(ptr, true);
    const bytes = new Uint8Array(this.memory.buffer, ptr + 4, len);
    return new TextDecoder().decode(bytes);
  }
}

export async function load(url) {
  const response = await fetch(url);
  const bytes = await response.arrayBuffer();
  const importObject = {
    wasi_snapshot_preview1: {
      fd_write: (fd, iovs, iovs_len, nwritten) => 0
    }
  };
  const result = await WebAssembly.instantiate(bytes, importObject);
  return new EchidnaTEA(result.instance.exports);
}

export const Msg = {
  Navigate: (dept) => ({ tag: 0, value: dept }),
  PopState: () => ({ tag: 1 })
};

// Internal Wasm tags for Msg
export const MsgTag = {
  Navigate: 0,
  PopState: 1
};

export const Department = {
  Provers: 0,
  TrustPipeline: 1,
  NeuralSearch: 2,
  FormalSpecs: 3
};
