// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Graphics coprocessor — 2-D SVG rendering, no GPU dependency.
//!
//! Backs the proof-graph visualisation that the GNN-guided search consumes,
//! and renders Pareto-frontier diagnostics + tactic-frequency bar charts
//! for the supervisor's status dashboards.
//!
//! Pure Rust, zero deps — emits SVG strings directly.  No `svg` crate
//! dependency because our needs are small and the wire format is the SVG
//! source itself (consumed downstream by browsers, Chromium-headless,
//! or any SVG viewer).

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::fmt::Write;

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

pub struct GraphicsBackend {
    capabilities: CoprocessorCapabilities,
}

impl GraphicsBackend {
    pub fn new() -> Self {
        GraphicsBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "GraphicsProofGraphSvg".into(),
                    "GraphicsBarChartSvg".into(),
                ],
                typical_latency_us: 200,
                deterministic: true,
            },
        }
    }
}

impl Default for GraphicsBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for GraphicsBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Graphics
    }
    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }
    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }
    fn trust_tier(&self) -> CoprocessorTrustTier {
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("graphics join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::GraphicsProofGraphSvg { nodes, edges } => {
            CoprocessorOutcome::Hex(hex_str(&render_proof_graph(&nodes, &edges)))
        }
        CoprocessorOp::GraphicsBarChartSvg { title, bars } => {
            CoprocessorOutcome::Hex(hex_str(&render_bar_chart(&title, &bars)))
        }
        other => CoprocessorOutcome::Failure(format!(
            "Graphics backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

/// Hex-encode an SVG string so it travels through `CoprocessorOutcome::Hex`
/// without escaping concerns at the wire layer.  Caller decodes once on
/// receipt.  Trade-off: 2× wire size; benefit: no JSON-string-escape
/// fragility on `<` `>` `"` etc. which abound in SVG.
fn hex_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for b in s.bytes() {
        write!(out, "{:02x}", b).unwrap();
    }
    out
}

/// Vertical-waterfall layout: sort by approximate topological depth, place
/// nodes on rows, edges as straight lines.  Deliberately simple — Phase 7
/// will replace with a proper layout engine if needed.
fn render_proof_graph(nodes: &[(String, String)], edges: &[(String, String)]) -> String {
    let n = nodes.len();
    if n == 0 {
        return r#"<svg xmlns="http://www.w3.org/2000/svg" width="100" height="40"><text x="10" y="25" font-family="sans-serif" font-size="12">empty</text></svg>"#.into();
    }
    // Compute approximate depth: longest incoming edge chain (BFS from sources).
    let depths = compute_depths(nodes, edges);
    let row_count = (depths.iter().copied().max().unwrap_or(0) + 1) as usize;
    let cell_w = 160usize;
    let cell_h = 60usize;
    let width = cell_w * n.max(1);
    let height = cell_h * row_count.max(1) + 40;

    // Position lookup: id → (x, y).
    let mut pos = std::collections::HashMap::<String, (usize, usize)>::new();
    let mut row_cursor = vec![0usize; row_count];
    for (i, (id, _label)) in nodes.iter().enumerate() {
        let d = depths[i] as usize;
        let col = row_cursor[d];
        row_cursor[d] += 1;
        let x = col * cell_w + cell_w / 2;
        let y = d * cell_h + 30;
        pos.insert(id.clone(), (x, y));
    }

    let mut svg = String::new();
    write!(
        svg,
        r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
    )
    .unwrap();
    write!(svg, r#"<style>.node{{fill:#003a3a;stroke:#fff;stroke-width:2}}.label{{fill:#fff;font-family:sans-serif;font-size:11px;text-anchor:middle}}.edge{{stroke:#888;stroke-width:1.5;fill:none}}</style>"#).unwrap();

    // Edges first (so nodes draw on top).
    for (from, to) in edges {
        if let (Some(&(x1, y1)), Some(&(x2, y2))) = (pos.get(from), pos.get(to)) {
            write!(svg, r#"<line class="edge" x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}"/>"#).unwrap();
        }
    }

    // Nodes.
    for (id, label) in nodes {
        if let Some(&(x, y)) = pos.get(id) {
            write!(
                svg,
                r#"<rect class="node" x="{}" y="{}" width="120" height="32" rx="6"/>"#,
                x as i64 - 60,
                y as i64 - 16
            )
            .unwrap();
            write!(
                svg,
                r#"<text class="label" x="{x}" y="{}">{}</text>"#,
                y + 4,
                escape_xml(label)
            )
            .unwrap();
        }
    }
    svg.push_str("</svg>");
    svg
}

fn compute_depths(nodes: &[(String, String)], edges: &[(String, String)]) -> Vec<u32> {
    use std::collections::HashMap;
    let n = nodes.len();
    let id_to_idx: HashMap<&str, usize> =
        nodes.iter().enumerate().map(|(i, (id, _))| (id.as_str(), i)).collect();
    let mut depth = vec![0u32; n];
    // Iterate to fixpoint — n iterations suffice for a DAG; if cyclic,
    // depths plateau (no infinite loop).
    for _ in 0..n {
        let mut changed = false;
        for (from, to) in edges {
            if let (Some(&fi), Some(&ti)) = (id_to_idx.get(from.as_str()), id_to_idx.get(to.as_str())) {
                let candidate = depth[fi] + 1;
                if candidate > depth[ti] {
                    depth[ti] = candidate;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    depth
}

fn render_bar_chart(title: &str, bars: &[(String, f64)]) -> String {
    if bars.is_empty() {
        return format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="200" height="40"><text x="10" y="25" font-family="sans-serif" font-size="12">{}: empty</text></svg>"#,
            escape_xml(title)
        );
    }
    let bar_w = 40usize;
    let gap = 10usize;
    let chart_h = 200usize;
    let n = bars.len();
    let width = n * (bar_w + gap) + gap;
    let height = chart_h + 60;
    let max = bars
        .iter()
        .map(|(_, h)| *h)
        .fold(0.0f64, |a, b| if b > a { b } else { a })
        .max(1.0);

    let mut svg = String::new();
    write!(
        svg,
        r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
    )
    .unwrap();
    write!(svg, r#"<style>.bar{{fill:#003a3a}}.title{{font-family:sans-serif;font-size:14px;font-weight:600}}.lbl{{font-family:sans-serif;font-size:10px;text-anchor:middle}}</style>"#).unwrap();
    write!(svg, r#"<text class="title" x="{gap}" y="20">{}</text>"#, escape_xml(title)).unwrap();

    for (i, (label, h)) in bars.iter().enumerate() {
        let x = gap + i * (bar_w + gap);
        let normalised_h = ((h / max) * chart_h as f64) as i64;
        let y = 30 + chart_h as i64 - normalised_h;
        write!(svg, r#"<rect class="bar" x="{x}" y="{y}" width="{bar_w}" height="{normalised_h}"/>"#).unwrap();
        write!(
            svg,
            r#"<text class="lbl" x="{}" y="{}">{}</text>"#,
            x + bar_w / 2,
            30 + chart_h + 14,
            escape_xml(label)
        )
        .unwrap();
    }
    svg.push_str("</svg>");
    svg
}

fn escape_xml(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(op: CoprocessorOp) -> CoprocessorOutcome {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        rt.block_on(async {
            GraphicsBackend::new().dispatch(op).await.unwrap()
        })
    }

    fn decode_hex(h: &str) -> String {
        let bytes: Vec<u8> = (0..h.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
            .collect();
        String::from_utf8(bytes).unwrap()
    }

    #[test]
    fn proof_graph_emits_svg_with_nodes_and_edges() {
        let nodes = vec![
            ("a".into(), "Goal".into()),
            ("b".into(), "Lemma".into()),
            ("c".into(), "Axiom".into()),
        ];
        let edges = vec![
            ("a".into(), "b".into()),
            ("b".into(), "c".into()),
        ];
        match run(CoprocessorOp::GraphicsProofGraphSvg { nodes, edges }) {
            CoprocessorOutcome::Hex(h) => {
                let svg = decode_hex(&h);
                assert!(svg.starts_with("<svg "));
                assert!(svg.ends_with("</svg>"));
                assert!(svg.contains("Goal"));
                assert!(svg.contains("Lemma"));
                assert!(svg.contains("Axiom"));
                assert!(svg.contains("<line"));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn empty_proof_graph_renders_placeholder() {
        match run(CoprocessorOp::GraphicsProofGraphSvg {
            nodes: vec![],
            edges: vec![],
        }) {
            CoprocessorOutcome::Hex(h) => {
                let svg = decode_hex(&h);
                assert!(svg.contains("empty"));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn bar_chart_includes_title_and_bars() {
        match run(CoprocessorOp::GraphicsBarChartSvg {
            title: "tactic frequency".into(),
            bars: vec![
                ("auto".into(), 12.0),
                ("simpl".into(), 7.0),
                ("apply".into(), 5.0),
            ],
        }) {
            CoprocessorOutcome::Hex(h) => {
                let svg = decode_hex(&h);
                assert!(svg.contains("tactic frequency"));
                assert!(svg.contains("auto"));
                assert!(svg.contains("simpl"));
                assert!(svg.contains("<rect"));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn xml_escape_handles_special_chars() {
        match run(CoprocessorOp::GraphicsBarChartSvg {
            title: "<dangerous & \"chars\">".into(),
            bars: vec![("k".into(), 1.0)],
        }) {
            CoprocessorOutcome::Hex(h) => {
                let svg = decode_hex(&h);
                assert!(svg.contains("&lt;dangerous &amp; &quot;chars&quot;&gt;"));
                assert!(!svg.contains("<dangerous"));
            }
            _ => panic!(),
        }
    }
}
