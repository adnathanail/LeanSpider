// TypeScript port of the former zxRender.py: builds a D3-ready graph object
// from the Lean diagram JSON, replacing pyzx + Pyodide.

export interface DiagramNode {
  id: number
  type: 'spider' | 'input' | 'output' | 'hadamard' | 'wire'
  color?: 'Z' | 'X'
  phase?: string
  ioId?: number
  /** Pre-computed column from the algebraic ZX walker. When present on
   *  any node, autoLayout is skipped — every node is expected to carry
   *  both `col` and `qubit`. */
  col?: number
  qubit?: number
}

export interface DiagramEdge {
  src: number
  tgt: number
}

/** The set of node ids inside a `stack` or `compose` subtree, emitted by
 *  the Lean walker. The viewer computes pixel bounds from each node's live
 *  position so boxes follow drags and don't extend into spliced-wire space. */
export interface DiagramBox {
  kind: 'stack' | 'compose'
  nodeIds: number[]
}

export interface DiagramData {
  nodes: DiagramNode[]
  edges: DiagramEdge[]
  boxes?: DiagramBox[]
}

export interface GraphNode {
  name: string
  x: number
  y: number
  t: number
  phase: string
  ground: boolean
  vdata: [string, unknown][]
}

export interface GraphLink {
  source: string
  target: string
  t: number
  index: number
  num_parallel: number
}

export interface GraphData {
  nodes: GraphNode[]
  links: GraphLink[]
  pauli_web: never[]
}

/** A box passed through to `zxViewer.js` unchanged; pixel bounds are
 *  computed there from live node positions so they follow drags. */
export interface RenderBox {
  kind: 'stack' | 'compose'
  nodeIds: number[]
}

export interface RenderData {
  graph: GraphData
  width: number
  height: number
  scale: number
  node_size: number
  colors: Record<string, string>
  /** Whether the viewer should auto-position H-boxes at the barycentre of
   *  their neighbours. False when positions came pre-computed from the
   *  algebraic ZX walker — otherwise hadamards' supplied positions get
   *  overwritten on every paint. */
  auto_hbox: boolean
  /** Bounding rectangles for `stack`/`compose` subtrees, sorted largest-area
   *  first so outer boxes paint behind inner ones. */
  boxes: RenderBox[]
}

const VertexType = { BOUNDARY: 0, Z: 1, X: 2, H_BOX: 3, WIRE: 4 } as const
const EdgeType = { SIMPLE: 1 } as const

// pyzx.utils.original_colors
const COLORS: Record<string, string> = {
  edge: '#000000',
  Hedge: '#0088ff',
  Xedge: '#999999',
  boundary: '#000000',
  X: '#ff8888',
  Y: '#aabbff',
  Z: '#ccffcc',
  H: '#ffff66',
  W: '#000000',
  Zalt: '#ccffcc',
  Walt: '#000000',
  Xdark: '#ff8888',
  Ydark: '#aabbff',
  Zdark: '#99dd99',
}

function gcd(a: number, b: number): number {
  let x = Math.abs(a)
  let y = Math.abs(b)
  while (y) {
    const t = y
    y = x % y
    x = t
  }
  return x || 1
}

interface Phase {
  num: number
  den: number
}

function parsePhase(s: string | undefined): Phase {
  const str = (s ?? '0').trim()
  let num: number
  let den: number
  if (str.includes('/')) {
    const [n, d] = str.split('/')
    num = Number.parseInt(n, 10)
    den = Number.parseInt(d, 10)
  } else {
    num = Number.parseInt(str, 10)
    den = 1
  }
  if (den < 0) {
    num = -num
    den = -den
  }
  const g = gcd(num, den)
  return { num: num / g, den: den / g }
}

// pyzx.utils.phase_fraction_to_s for spiders/H-boxes (poly_with_pi irrelevant
// here because Lean phases are always rational).
function phaseToString(p: Phase, t: number): string {
  const isHBox = t === VertexType.H_BOX
  if (p.num === 0 && !isHBox) return ''
  if (p.num === p.den && isHBox) return ''
  if (p.num === 0) return '0'
  const ns = p.num === 1 ? '' : String(p.num)
  const ds = p.den === 1 ? '' : `/${String(p.den)}`
  return `${ns}π${ds}`
}

interface InternalNode {
  id: number
  t: number
  row: number | null
  qubit: number | null
  phaseStr: string
  isInput: boolean
  isOutput: boolean
}

function buildNodes(diagram: DiagramData): Map<number, InternalNode> {
  const out = new Map<number, InternalNode>()
  for (const n of diagram.nodes) {
    let t: number
    let row: number | null = null
    let qubit: number | null = null
    let phaseStr = ''
    let isInput = false
    let isOutput = false

    if (n.type === 'input') {
      t = VertexType.BOUNDARY
      row = n.col ?? 0
      qubit = n.qubit ?? n.ioId ?? 0
      isInput = true
    } else if (n.type === 'output') {
      t = VertexType.BOUNDARY
      row = n.col ?? -1
      qubit = n.qubit ?? n.ioId ?? 0
      isOutput = true
    } else if (n.type === 'spider') {
      t = n.color === 'X' ? VertexType.X : VertexType.Z
      if (n.col !== undefined) row = n.col
      if (n.qubit !== undefined) qubit = n.qubit
      phaseStr = phaseToString(parsePhase(n.phase), t)
    } else if (n.type === 'hadamard') {
      t = VertexType.H_BOX
      if (n.col !== undefined) row = n.col
      if (n.qubit !== undefined) qubit = n.qubit
      phaseStr = phaseToString(parsePhase(n.phase ?? '1'), t)
    } else if (n.type === 'wire') {
      t = VertexType.WIRE
      if (n.col !== undefined) row = n.col
      if (n.qubit !== undefined) qubit = n.qubit
    } else {
      t = VertexType.BOUNDARY
    }
    out.set(n.id, { id: n.id, t, row, qubit, phaseStr, isInput, isOutput })
  }
  return out
}

function autoLayout(nodes: Map<number, InternalNode>, edges: DiagramEdge[]): void {
  const inputs: number[] = []
  const outputs: number[] = []
  for (const n of nodes.values()) {
    if (n.isInput) inputs.push(n.id)
    if (n.isOutput) outputs.push(n.id)
  }
  if (inputs.length === 0) return

  const adj = new Map<number, number[]>()
  for (const id of nodes.keys()) adj.set(id, [])
  for (const e of edges) {
    adj.get(e.src)?.push(e.tgt)
    adj.get(e.tgt)?.push(e.src)
  }

  // BFS depth from inputs
  const depth = new Map<number, number>()
  const queue: number[] = []
  for (const id of inputs) {
    depth.set(id, 0)
    queue.push(id)
  }
  while (queue.length) {
    const cur = queue.shift() as number
    const curDepth = depth.get(cur) ?? 0
    for (const nb of adj.get(cur) ?? []) {
      if (!depth.has(nb)) {
        depth.set(nb, curDepth + 1)
        queue.push(nb)
      }
    }
  }

  let maxDepth = 1
  for (const d of depth.values()) if (d > maxDepth) maxDepth = d

  // Assign rows: interior non-H-box vertices get BFS depth; outputs get maxDepth.
  // H-boxes get no row (positioned by auto_hbox in the viewer).
  for (const [id, d] of depth) {
    const n = nodes.get(id)
    if (!n) continue
    if (!n.isInput && !n.isOutput && n.t !== VertexType.H_BOX) {
      n.row = d
    }
  }
  for (const id of outputs) {
    const n = nodes.get(id)
    if (n) n.row = maxDepth
  }

  // Qubit assignment: interior non-H-box vertices fill the lowest free slot per
  // row, skipping qubit indices already claimed by boundary nodes on that row.
  const rowTaken = new Map<number, Set<number>>()
  const claim = (row: number, q: number) => {
    let s = rowTaken.get(row)
    if (!s) {
      s = new Set()
      rowTaken.set(row, s)
    }
    s.add(q)
  }
  for (const id of [...inputs, ...outputs]) {
    const n = nodes.get(id)
    if (n && n.row !== null && n.qubit !== null) claim(n.row, n.qubit)
  }

  const rowCounts = new Map<number, number>()
  // Iterate in id order (matches pyzx's GraphS.vertices() ordering).
  const sortedIds = [...nodes.keys()].sort((a, b) => a - b)
  for (const id of sortedIds) {
    const n = nodes.get(id)
    if (!n) continue
    if (n.isInput || n.isOutput || n.t === VertexType.H_BOX) continue
    if (n.row === null) continue
    let count = rowCounts.get(n.row) ?? 0
    const taken = rowTaken.get(n.row) ?? new Set<number>()
    while (taken.has(count)) count++
    n.qubit = count
    rowCounts.set(n.row, count + 1)
  }
}

function pairKey(a: number, b: number): string {
  return a < b ? `${a}|${b}` : `${b}|${a}`
}

export function render(diagram: DiagramData): RenderData {
  const nodes = buildNodes(diagram)
  const positioned = diagram.nodes.some(n => n.col !== undefined)
  if (!positioned) autoLayout(nodes, diagram.edges)

  // Skip H-boxes (no row/qubit) when computing the bounds.
  let minrow = Number.POSITIVE_INFINITY
  let maxrow = Number.NEGATIVE_INFINITY
  let minqub = Number.POSITIVE_INFINITY
  let maxqub = Number.NEGATIVE_INFINITY
  for (const n of nodes.values()) {
    if (n.row === null || n.qubit === null) continue
    if (n.row < minrow) minrow = n.row
    if (n.row > maxrow) maxrow = n.row
    if (n.qubit < minqub) minqub = n.qubit
    if (n.qubit > maxqub) maxqub = n.qubit
  }
  if (!Number.isFinite(minrow)) {
    minrow = 0
    maxrow = 0
    minqub = 0
    maxqub = 0
  }

  let scale = 800 / (maxrow - minrow + 2)
  if (scale > 50) scale = 50
  if (scale < 20) scale = 20

  const width = (maxrow - minrow + 2) * scale
  const height = (maxqub - minqub + 3) * scale
  const node_size = Math.max(0.2 * scale, 2)

  // Emit nodes in id order. H-boxes without a row land at the top-left
  // placeholder coordinate; the viewer's update_hboxes() repositions them
  // before the first paint.
  const sortedIds = [...nodes.keys()].sort((a, b) => a - b)
  const outNodes: GraphNode[] = sortedIds.map(id => {
    const n = nodes.get(id) as InternalNode
    const row = n.row ?? 0
    const qubit = n.qubit ?? 0
    return {
      name: String(n.id),
      x: (row - minrow + 1) * scale,
      y: (qubit - minqub + 2) * scale,
      t: n.t,
      phase: n.phaseStr,
      ground: false,
      vdata: [],
    }
  })

  // Parallel edge metadata: group by unordered endpoint pair so (a,b) and (b,a)
  // count as parallel. Mirrors pyzx.drawing.graph_json's index/num_parallel.
  const counts = new Map<string, number>()
  const linkKeys: string[] = []
  const links: GraphLink[] = diagram.edges.map(e => {
    const k = pairKey(e.src, e.tgt)
    const i = counts.get(k) ?? 0
    counts.set(k, i + 1)
    linkKeys.push(k)
    return {
      source: String(e.src),
      target: String(e.tgt),
      t: EdgeType.SIMPLE,
      index: i,
      num_parallel: 0,
    }
  })
  for (let i = 0; i < links.length; i++) {
    links[i].num_parallel = counts.get(linkKeys[i]) ?? 1
  }

  // Boxes pass through unchanged. Pixel bounds are computed in zxViewer.js
  // from live node positions. Sort largest first (id-count is a proxy for
  // area since parents strictly contain children) so outer paints behind.
  const boxes: RenderBox[] = (diagram.boxes ?? []).map(b => ({
    kind: b.kind,
    nodeIds: b.nodeIds,
  }))
  boxes.sort((a, b) => b.nodeIds.length - a.nodeIds.length)

  return {
    graph: { nodes: outNodes, links, pauli_web: [] },
    width,
    height,
    scale,
    node_size,
    colors: COLORS,
    auto_hbox: !positioned,
    boxes,
  }
}
