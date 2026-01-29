// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * ProofTree component - Visualize proof tree structure
 * Shows hierarchical proof structure with interactive navigation
 */

@react.component
let make = () => {
  let (treeData, setTreeData) = React.useState(() => None)
  let (isLoading, setIsLoading) = React.useState(() => false)
  let (expandedNodes, setExpandedNodes) = React.useState(() => Belt.Set.String.empty)

  // Fetch proof tree on mount
  React.useEffect(() => {
    setIsLoading(_ => true)
    let _ = Client.getProofTree()|> Js.Promise.then_(result => {
      switch result {
      | Ok(data) => {
          setTreeData(_ => Some(data))
          setIsLoading(_ => false)
          Js.Promise.resolve(())
        }
      | Error(_) => {
          setTreeData(_ => None)
          setIsLoading(_ => false)
          Js.Promise.resolve(())
        }
      }
    })
    None
  }, [])

  let toggleNode = nodeId => {
    setExpandedNodes(prev => {
      if Belt.Set.String.has(prev, nodeId) {
        Belt.Set.String.remove(prev, nodeId)
      } else {
        Belt.Set.String.add(prev, nodeId)
      }
    })
  }

  // JSON decode helpers
  let getStringField = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeString)
    ->Belt.Option.getWithDefault("")

  let getArrayField = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeArray)
    ->Belt.Option.getWithDefault([])

  let rec renderTreeNode = (~node: Js.Json.t, ~depth: int) => {
    switch Js.Json.decodeObject(node) {
    | Some(dict) => {
        let nodeId = getStringField(dict, "id")
        let nodeType = getStringField(dict, "type")
        let label = getStringField(dict, "label")
        let children = getArrayField(dict, "children")

        let hasChildren = Array.length(children) > 0
        let isExpanded = Belt.Set.String.has(expandedNodes, nodeId)
        let indent = Belt.Int.toString(depth * 20) ++ "px"

        let nodeColor = switch nodeType {
        | "goal" => "bg-blue-100 border-blue-500"
        | "tactic" => "bg-green-100 border-green-500"
        | "lemma" => "bg-purple-100 border-purple-500"
        | "axiom" => "bg-yellow-100 border-yellow-500"
        | _ => "bg-gray-100 border-gray-500"
        }

        <div key=nodeId className="tree-node mb-2">
        <div
          className={`node-content p-3 rounded-lg border-l-4 ${nodeColor} cursor-pointer hover:shadow-md transition-shadow`}
          style={{marginLeft: indent}}
          onClick={_ => if hasChildren {
            toggleNode(nodeId)
          }}>
          <div className="flex items-center">
            {if hasChildren {
              <span className="mr-2 text-gray-600">
                {React.string(isExpanded ? "▼" : "▶")}
              </span>
            } else {
              <span className="mr-2 text-gray-400"> {React.string("•")} </span>
            }}
            <span className="text-xs font-semibold text-gray-600 mr-2">
              {React.string(Js.String.toUpperCase(nodeType))}
            </span>
            <code className="text-sm font-mono text-gray-900"> {React.string(label)} </code>
          </div>
        </div>

        {if hasChildren && isExpanded {
          <div className="node-children mt-2">
            {Belt.Array.map(children, child => renderTreeNode(~node=child, ~depth=depth + 1))->React.array}
          </div>
        } else {
          React.null
        }}
        </div>
      }
    | None => React.null
    }
  }

  let expandAll = () => {
    // Recursively collect all node IDs
    let rec collectIds = (node: Js.Json.t): array<string> => {
      switch Js.Json.decodeObject(node) {
      | Some(dict) => {
          let id = getStringField(dict, "id")
          let children = getArrayField(dict, "children")
          let childIds = Belt.Array.map(children, collectIds)->Belt.Array.concatMany
          Belt.Array.concat([id], childIds)
        }
      | None => []
      }
    }

    switch treeData {
    | Some(data) => {
        let allIds = collectIds(data)
        setExpandedNodes(_ => Belt.Set.String.fromArray(allIds))
      }
    | None => ()
    }
  }

  let collapseAll = () => {
    setExpandedNodes(_ => Belt.Set.String.empty)
  }

  <div className="proof-tree">
    <div className="header mb-4">
      <div className="flex justify-between items-center">
        <div>
          <h2 className="text-2xl font-bold text-gray-900"> {React.string("Proof Tree")} </h2>
          <p className="text-sm text-gray-600">
            {React.string("Hierarchical view of proof structure")}
          </p>
        </div>
        <div className="controls flex gap-2">
          <button
            className="px-3 py-1 text-sm bg-gray-200 text-gray-700 rounded hover:bg-gray-300 transition-colors"
            onClick={_ => expandAll()}>
            {React.string("Expand All")}
          </button>
          <button
            className="px-3 py-1 text-sm bg-gray-200 text-gray-700 rounded hover:bg-gray-300 transition-colors"
            onClick={_ => collapseAll()}>
            {React.string("Collapse All")}
          </button>
        </div>
      </div>
    </div>

    {if isLoading {
      <div className="loading p-8 text-center">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto mb-4" />
        <p className="text-gray-600"> {React.string("Loading proof tree...")} </p>
      </div>
    } else {
      switch treeData {
      | Some(data) =>
        <div className="tree-container bg-white border border-gray-300 rounded-lg p-4 max-h-96 overflow-y-auto">
          {renderTreeNode(~node=data, ~depth=0)}
        </div>
      | None =>
        <div className="no-tree p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
          <p className="text-gray-600"> {React.string("No proof tree available")} </p>
          <p className="text-sm text-gray-500 mt-2">
            {React.string("Start a proof to see the tree structure")}
          </p>
        </div>
      }
    }}

    <div className="legend mt-4 p-4 bg-gray-50 border border-gray-200 rounded-lg">
      <h3 className="font-bold text-sm text-gray-900 mb-2">
        {React.string("Node Types")}
      </h3>
      <div className="grid grid-cols-2 md:grid-cols-4 gap-2">
        <div className="flex items-center">
          <div className="w-4 h-4 bg-blue-500 rounded mr-2" />
          <span className="text-xs text-gray-700"> {React.string("Goal")} </span>
        </div>
        <div className="flex items-center">
          <div className="w-4 h-4 bg-green-500 rounded mr-2" />
          <span className="text-xs text-gray-700"> {React.string("Tactic")} </span>
        </div>
        <div className="flex items-center">
          <div className="w-4 h-4 bg-purple-500 rounded mr-2" />
          <span className="text-xs text-gray-700"> {React.string("Lemma")} </span>
        </div>
        <div className="flex items-center">
          <div className="w-4 h-4 bg-yellow-500 rounded mr-2" />
          <span className="text-xs text-gray-700"> {React.string("Axiom")} </span>
        </div>
      </div>
    </div>
  </div>
}
