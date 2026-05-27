import '@fontsource/inter/latin-400.css';
import '@fontsource/inter/latin-700.css';
import './styles.css';
import {
  AmbientLight,
  BoxGeometry,
  BufferAttribute,
  BufferGeometry,
  CatmullRomCurve3,
  CircleGeometry,
  Clock,
  Color,
  DirectionalLight,
  DoubleSide,
  DynamicDrawUsage,
  Fog,
  Group,
  InstancedMesh,
  Line,
  LineBasicMaterial,
  LineDashedMaterial,
  LineSegments,
  Matrix4,
  Mesh,
  MeshBasicMaterial,
  MeshPhysicalMaterial,
  OctahedronGeometry,
  PerspectiveCamera,
  PlaneGeometry,
  Quaternion,
  Raycaster,
  Scene,
  SphereGeometry,
  TetrahedronGeometry,
  TorusGeometry,
  Vector2,
  Vector3,
  WebGLRenderer,
} from 'three';
import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls.js';
import { LineSegments2 } from 'three/examples/jsm/lines/LineSegments2.js';
import { LineSegmentsGeometry } from 'three/examples/jsm/lines/LineSegmentsGeometry.js';
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js';
import {
  CornerUpLeft,
  Pause,
  Play,
  RotateCcw,
  Route,
  createIcons,
} from 'lucide';

createIcons({ icons: { CornerUpLeft, Pause, Play, RotateCcw, Route } });

const canvas = document.querySelector('#scene');
const backView = document.querySelector('#backView');
const playToggle = document.querySelector('#playToggle');
const rerouteButton = document.querySelector('#reroute');
const resetViewButton = document.querySelector('#resetView');
const crumbs = document.querySelector('#crumbs');
const messageLabel = document.querySelector('#messageLabel');
const messageMeta = document.querySelector('#messageMeta');
const currentPosition = document.querySelector('#currentPosition');
const overviewMap = document.querySelector('#overviewMap');
const budgetRange = document.querySelector('#budgetRange');
const budgetValue = document.querySelector('#budgetValue');
const metricVariant = document.querySelector('#metricVariant');
const metricFamily = document.querySelector('#metricFamily');
const metricSig = document.querySelector('#metricSig');
const metricVerify = document.querySelector('#metricVerify');
const metricSign = document.querySelector('#metricSign');
const metricSecurity = document.querySelector('#metricSecurity');
const paramGrid = document.querySelector('#paramGrid');
const nodeType = document.querySelector('#nodeType');
const nodeTitle = document.querySelector('#nodeTitle');
const nodeMeta = document.querySelector('#nodeMeta');
const variantButtons = [...document.querySelectorAll('.variant-button')];

// All numbers below mirror the README + write-up tables exactly.
// Family / hash kernel naming follows FIPS 205 (SLH-DSA standard) and ePrint 2025/2203 (WOTS+C / FORS+C).
const params = {
  c7: {
    label: 'C7',
    family: 'WOTS+C / FORS+C',
    hash: 'keccak256 / 32-B JARDIN ADRS',
    h: 24, d: 2, a: 16, k: 8, w: 8, l: 43, n: 16, swn: 151,
    sig: '3,704 B',
    sigBytes: 3704,
    verify: '127 K',
    verifyGas: 127_000,
    signH: '4.3 M',
    sec: { 10: 128, 14: 128, 18: 128, 20: 128 },
    color: '#7cfcbd',
  },
  c11: {
    label: 'C11',
    family: 'WOTS+C / FORS+C',
    hash: 'keccak256 / 32-B JARDIN ADRS',
    h: 16, d: 2, a: 11, k: 13, w: 8, l: 43, n: 16, swn: 203,
    sig: '3,976 B',
    sigBytes: 3976,
    verify: '116 K',
    verifyGas: 116_000,
    signH: '292 K',
    sec: { 10: 128, 14: 128, 18: 104.5, 20: 86.1 },
    color: '#ffcf8c',
  },
  c12: {
    label: 'C12',
    family: 'vanilla SPHINCS+ (SPX)',
    hash: 'keccak256 / 32-B JARDIN ADRS',
    h: 20, d: 5, a: 7, k: 20, w: 8, l: 45, n: 16, swn: null,
    sig: '6,512 B',
    sigBytes: 6512,
    verify: '276 K',
    verifyGas: 276_000,
    signH: '36.6 K',
    sec: { 10: 128, 14: 127.8, 18: 109.1, 20: 95.4 },
    color: '#61d6ff',
  },
  'slh-sha2': {
    label: 'SLH·SHA2',
    family: 'SLH-DSA-SHA2-128-24 (FIPS 205 + SP 800-230 IPD)',
    hash: 'SHA-256 precompile / 22-B ADRSc + MGF1 Hmsg',
    h: 22, d: 1, a: 24, k: 6, w: 4, l: 68, n: 16, swn: null,
    sig: '3,856 B',
    sigBytes: 3856,
    verify: '~142 K*',
    verifyGas: 142_000,
    signH: '~1.07 B',
    sec: { 10: 128, 14: 128, 18: 128, 20: 128 },
    color: '#b264ff',
  },
  'slh-keccak': {
    label: 'SLH·Kec',
    family: 'SLH-DSA-Keccak-128-24 (JARDIN twin)',
    hash: 'keccak256 opcode / 32-B JARDIN ADRS, Hmsg = keccak(seed‖root‖R‖msg‖0xFF..FB)',
    h: 22, d: 1, a: 24, k: 6, w: 4, l: 68, n: 16, swn: null,
    sig: '3,856 B',
    sigBytes: 3856,
    verify: '~94 K*',
    verifyGas: 94_000,
    signH: '~1.07 B',
    sec: { 10: 128, 14: 128, 18: 128, 20: 128 },
    color: '#ff7ad9',
  },
};

const palette = {
  root: new Color('#ffffff'),
  xmss: new Color('#7cfcbd'),
  wots: new Color('#f35f8f'),
  fors: new Color('#61d6ff'),
  path: new Color('#ffcf8c'),
  quiet: new Color('#26312e'),
  edge: new Color('#3d4c49'),
};

const state = {
  variantKey: 'c7',
  view: { type: 'hypertree', label: 'Hypertree', depth: 0, seed: 9 },
  stack: [],
  playing: true,
  routeSeed: 9,
  routeCursor: 0,
  budgetExponent: Number(budgetRange.value),
  hoverId: null,
};

const scene = new Scene();
scene.fog = new Fog(0x07090b, 14, 48);

const camera = new PerspectiveCamera(46, window.innerWidth / window.innerHeight, 0.1, 220);
// 2D-style view: camera looks straight down the z-axis at the (x, y) plane.
// Initial position is overwritten by resetExplorer/focusScene with the variant's
// midpoint so the scene is centred regardless of d.
camera.position.set(0, 0, 24);
camera.up.set(0, 1, 0);

const renderer = new WebGLRenderer({
  canvas,
  antialias: true,
  alpha: false,
  preserveDrawingBuffer: true,
  powerPreference: 'high-performance',
});
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.setClearColor(0x07090b, 1);

const controls = new OrbitControls(camera, canvas);
controls.enableDamping = true;
controls.dampingFactor = 0.08;
controls.minDistance = 4;
controls.maxDistance = 70;
// 2D mode — disable orbital rotation so the scene reads as a flat diagram.
// Pan + zoom remain so the user can navigate.
controls.enableRotate = false;
controls.screenSpacePanning = true;
controls.target.set(0, 0, 0);

scene.add(new AmbientLight(0xc4ffe0, 0.44));
const keyLight = new DirectionalLight(0xffffff, 1.35);
keyLight.position.set(4, 9, 7);
scene.add(keyLight);
const rimLight = new DirectionalLight(0xffb359, 0.72);
rimLight.position.set(-9, 3, -4);
scene.add(rimLight);

// Camera-attached "ghost minimap" — populated only during drilldown views so
// the user keeps the global hypertree in sight. Camera must be added to the
// scene graph for its child groups to render.
scene.add(camera);
const minimapAnchor = new Group();
minimapAnchor.position.set(4.6, 3.0, -10);
minimapAnchor.scale.setScalar(0.16);
minimapAnchor.visible = false;
camera.add(minimapAnchor);

const world = new Group();
scene.add(world);

// Floor wireframe removed — implied a 3D ground plane that doesn't fit a
// 2D-style diagrammatic view.

const rootRing = new Mesh(
  new TorusGeometry(0.58, 0.009, 8, 96),
  new MeshBasicMaterial({ color: palette.path, transparent: true, opacity: 0.92 }),
);
world.add(rootRing);

// 2D shape system, family-keyed:
//   XMSS family (root / interior / leaf) → CIRCLE
//   WOTS+ family (pk / chain step / verifier triangle) → triangle pointing DOWN
//   FORS family  (pk / root / interior / leaf / sk) → SQUARE
const leafGeometry = new SphereGeometry(0.065, 16, 10); // legacy used by drilldown InstancedMesh leafMesh

// Circles (XMSS)
const xmssCircleGeometry = new CircleGeometry(0.1, 32);
const xmssCircleSmallGeometry = new CircleGeometry(0.06, 24);
const xmssCircleBigGeometry = new CircleGeometry(0.18, 40);

// Squares (FORS)
const forsSquareGeometry = new PlaneGeometry(0.16, 0.16);
const forsSquareSmallGeometry = new PlaneGeometry(0.1, 0.1);
const forsSquareBigGeometry = new PlaneGeometry(0.28, 0.28);

// Triangles pointing DOWN (WOTS+)
function makeDownTriangle(size) {
  const geom = new BufferGeometry();
  // equilateral, apex at bottom (y = -size). top edge at y = size/2.
  const h = size * Math.sqrt(3) / 2;
  geom.setAttribute('position', new BufferAttribute(new Float32Array([
    -size / 2, h / 2, 0,   // top-left
    size / 2, h / 2, 0,    // top-right
    0, -h / 2, 0,          // bottom apex
  ]), 3));
  geom.setIndex([0, 1, 2]);
  geom.computeVertexNormals();
  return geom;
}
const wotsTriangleGeometry = makeDownTriangle(0.22);
const wotsTriangleSmallGeometry = makeDownTriangle(0.14);
const wotsTriangleBigGeometry = makeDownTriangle(0.34);

function nodeFamily(node) {
  if (node.kind === 'fors-pk' || node.kind === 'fors-root' || node.kind === 'fors') return 'fors';
  if (node.kind === 'wots' || node.kind === 'wots-pk') return 'wots';
  // XMSS leaf = WOTS+ pk per FIPS 205 §3 — render as a triangle, drill into WOTS.
  if (node.id?.startsWith('tree-leaf-') && node.kind === 'xmss') return 'wots';
  return 'xmss';
}

function geometryForNode(node) {
  const family = nodeFamily(node);
  const isLeaf = node.id?.startsWith('tree-leaf-');
  const isBig = node.zoomable && (node.kind === 'root' || node.kind === 'fors-pk');
  // Tree leaves get the medium size whether zoomable or not — so a FORS active
  // leaf reads as a clearly-visible square, not a tiny dot.
  const isMid = node.zoomable || isLeaf;
  if (family === 'xmss') {
    return isBig ? xmssCircleBigGeometry : isMid ? xmssCircleGeometry : xmssCircleSmallGeometry;
  }
  if (family === 'fors') {
    return isBig ? forsSquareBigGeometry : isMid ? forsSquareGeometry : forsSquareSmallGeometry;
  }
  return isBig ? wotsTriangleBigGeometry : isMid ? wotsTriangleGeometry : wotsTriangleSmallGeometry;
}
const tmpMatrix = new Matrix4();
const tmpQuaternion = new Quaternion();
const tmpScale = new Vector3(1, 1, 1);

const allNodes = [];
const meshNodes = [];
const leafNodes = [];
const labelOnlyNodes = [];
const edgePairs = [];
// Parallel metadata arrays — describe what each edge cryptographically represents,
// so hovering a line shows e.g. "T_k aggregation: FORS pk = T_k(PK.seed, …)".
const edgeMeta = [];
const ghostMeshes = [];
const ghostEdgePairs = [];
const ghostEdgeMeta = [];
const dashedEdgePairs = [];        // active-path truncation dots (clickable to expand)
const ghostDashedEdgePairs = [];   // off-path truncation dots (visual only)

// Edge-meta presets keyed by cryptographic role, citing FIPS 205 sections.
const EDGE_META = {
  merkle_xmss: {
    kind: 'edge-merkle',
    title: 'XMSS Merkle hash H',
    meta: 'Interior XMSS node = H(PK.seed, ADRS, lnode ‖ rnode). Tweakable hash where ADRS encodes (layer, tree, type=TREE, height, index). FIPS 205 §6.1 / Algorithm 9.',
  },
  merkle_fors: {
    kind: 'edge-merkle',
    title: 'FORS interior H',
    meta: 'This edge belongs to the H step at the parent: parent = H(PK.seed, ADRS, lnode ‖ rnode). H is a tweakable hash combining two child nodes at interior levels (z ≥ 1). Note that the LEAF endpoint of this edge was itself computed via F(PK.seed, ADRS, sk) — different operator. FIPS 205 §8.2 / Algorithm 15 lines 9–11.',
  },
  fors_leaf: {
    kind: 'edge-merkle',
    title: 'FORS leaf hash F',
    meta: 'Leaf = F(PK.seed, ADRS, sk). Tweakable hash applied to the revealed n-byte secret value, producing one leaf of a FORS tree. FIPS 205 §8.2 / Algorithm 15 line 5.',
  },
  tk_fors: {
    kind: 'edge-tk',
    title: 'T_k aggregation → FORS pk',
    meta: 'FORS pk = T_k(PK.seed, ADRS_FORS_ROOTS, root_0 ‖ … ‖ root_{k-1}). T_k is a tweakable hash, NOT a plain hash with salt — its output depends on PK.seed AND on a structured ADRS (type=FORS_ROOTS, key-pair=idx_leaf at layer 0). FIPS 205 §8.4 Algorithm 17 line 24.',
  },
  wots_input: {
    kind: 'edge-wots-input',
    title: 'WOTS+ message input',
    meta: 'The value being signed by WOTS+ at this layer. d=0 signs the FORS pk; d=i (i>0) signs the XMSS d=i-1 root. wots_pkFromSig parses this message in base w to drive the chain advances. FIPS 205 §5.3 / Algorithm 8.',
  },
  wots_output: {
    kind: 'edge-wots-output',
    title: 'WOTS+ pk = XMSS leaf',
    meta: 'wots_pkFromSig output is the WOTS+ pk = T_l(PK.seed, ADRS, ep_0 ‖ … ‖ ep_{l-1}). This same value is the active leaf of the XMSS tree at this layer (per FIPS 205 §3: leaves of XMSS trees ARE WOTS+ pks).',
  },
  wots_chain_step: {
    kind: 'edge-wots',
    title: 'WOTS+ chain step',
    meta: 'F(PK.seed, ADRS, x) — one F application along a hash chain of length w-1=…. Each chain advances from sig[i] to position w-1, producing one chain endpoint. The verifier completes all l chains. FIPS 205 §5 / Algorithm 5 (chain).',
  },
  wots_compress: {
    kind: 'edge-wots',
    title: 'WOTS+ T_l compression',
    meta: 'WOTS+ pk = T_l(PK.seed, ADRS, ep_0 ‖ … ‖ ep_{l-1}). Tweakable hash compressing l chain endpoints into the single n-byte WOTS+ pk. FIPS 205 §5.1 / Algorithm 6.',
  },
};
const selectable = [];

// Per-tree-key extra revealed levels — clicking the "..." dots below a
// truncated tree increments the entry. Survives variant changes? No — cleared
// on variant change since trees are different. Keyed by `fors:${t}` / `xmss:${i}`.
const expandedLevelsByTree = new Map();
let edgeLines = null;
let ghostEdgeLines = null;
let routeLine = null;
let routeGeometry = null;
let currentRoute = [];
let currentRoot = null;
let cameraTween = null;
let inceptionTween = null;

// Iris-style overlay used during inception zoom transitions.
const inceptionOverlay = document.createElement('div');
inceptionOverlay.className = 'inception-overlay';
document.body.appendChild(inceptionOverlay);

// HTML overlay layer that holds per-node labels projected from 3D world space.
const labelLayer = document.createElement('div');
labelLayer.className = 'node-labels';
document.body.appendChild(labelLayer);

const _labelProj = new Vector3();

function makeNodeLabel(node) {
  if (!node.embedTitle && !node.embedInfo) return;
  const el = document.createElement('div');
  el.className = `node-label node-label-${node.kind}`;
  if (node.embedTitle) {
    const t = document.createElement('strong');
    t.textContent = node.embedTitle;
    el.appendChild(t);
  }
  if (node.embedInfo) {
    const i = document.createElement('em');
    i.textContent = node.embedInfo;
    el.appendChild(i);
  }
  labelLayer.appendChild(el);
  node.labelEl = el;
}

function disposeNodeLabel(node) {
  if (node.labelEl) {
    node.labelEl.remove();
    node.labelEl = null;
  }
}

function startInception(direction, focusPoint, onMid) {
  inceptionTween = {
    direction,
    focus: focusPoint.clone(),
    startedAt: performance.now(),
    duration: 520,
    phase: 'depart',
    onMid,
  };
}

const leafMaterial = new MeshPhysicalMaterial({ color: 0xffffff, roughness: 0.28, metalness: 0.16 });
const leafMesh = new InstancedMesh(leafGeometry, leafMaterial, 320);
leafMesh.instanceMatrix.setUsage(DynamicDrawUsage);
world.add(leafMesh);

const ghostMaterialCache = new Map();
function ghostMaterialFor(color) {
  const key = `${color.r}-${color.g}-${color.b}`;
  if (!ghostMaterialCache.has(key)) {
    ghostMaterialCache.set(
      key,
      new MeshBasicMaterial({ color: color.clone(), transparent: true, opacity: 0.32 }),
    );
  }
  return ghostMaterialCache.get(key);
}

// One generic Merkle-tree builder used by both the FORS forest and the XMSS layers.
// Draws a complete binary tree truncated to `visibleDepth` (so a tree of real
// depth h/d=22 still fits — we just show the top few levels and label the rest).
// Off-path nodes go into ONE InstancedMesh; the root, the active leaf, and any
// internal nodes on the active path are individually selectable mesh nodes.
function buildBinaryMerkleTree({
  rootPos,
  visibleDepth: requestedDepth,
  realDepth,
  width,
  height,
  color,
  activeLeafIdx,
  rootKind,
  rootKindIfTop,
  rootZoomable = true,
  rootTitle,
  rootMeta,
  leafKind,
  leafTitle,
  leafMeta,
  treeIndex,
  layerIndex,
  isTop = false,
  treeSeed,
}) {
  // Apply per-tree user expansion (dblclick on dashed truncation edge increments).
  const treeKey = layerIndex !== undefined && layerIndex >= 0
    ? `xmss:${layerIndex}`
    : `fors:${treeIndex ?? 0}`;
  const extraLevels = expandedLevelsByTree.get(treeKey) ?? 0;
  const baseRequested = Math.min(requestedDepth, realDepth);
  const requested = Math.min(requestedDepth + extraLevels, realDepth);
  const visibleDepth = Math.max(1, requested);
  const truncated = realDepth - visibleDepth;
  const leafCount = 1 << visibleDepth;
  const internalCount = (1 << visibleDepth) - 1;
  const leafIdx = ((activeLeafIdx % leafCount) + leafCount) % leafCount;
  // Levels strictly above baseRequested are "user-revealed" — render their
  // nodes thin (smaller baseScale) so they read as newly uncompressed.
  const isExpandedLevel = (level) => extraLevels > 0 && level > baseRequested;
  const expandedScale = 0.42;

  // Build position grid: positions[level][i].
  const positions = [];
  for (let level = 0; level <= visibleDepth; level += 1) {
    const count = 1 << level;
    const y = rootPos.y - (level / visibleDepth) * height;
    const row = [];
    for (let i = 0; i < count; i += 1) {
      const x = count === 1
        ? rootPos.x
        : rootPos.x + ((i + 0.5) / count - 0.5) * width;
      row.push(new Vector3(x, y, rootPos.z));
    }
    positions.push(row);
  }

  // Active path indices per level: idx = leafIdx >> (visibleDepth - level).
  const activeIdxByLevel = [];
  for (let level = 0; level <= visibleDepth; level += 1) {
    activeIdxByLevel.push(leafIdx >> (visibleDepth - level));
  }
  const activePath = activeIdxByLevel.map((idx, level) => positions[level][idx]);

  // Root = individual mesh (selectable).
  const rootKindResolved = isTop ? (rootKindIfTop ?? rootKind) : rootKind;
  const rootNode = addMeshNode({
    id: `tree-root-${rootKindResolved}-${layerIndex ?? 'L'}-${treeIndex ?? 'T'}-${treeSeed ?? 0}`,
    title: rootTitle,
    meta: rootMeta + (truncated > 0 ? ` (showing ${visibleDepth} of ${realDepth} levels — ${truncated} truncated.)` : ''),
    kind: rootKindResolved,
    zoomable: rootZoomable,
    color,
    layerIndex,
    treeIndex,
    seed: 50 + (treeSeed ?? 0),
    baseScale: isTop ? 1.18 : 1.0,
    position: positions[0][0],
  });

  // Active leaf = individual mesh (selectable). XMSS leaves are zoomable
  // (they ARE the WOTS+ pk → drilling lands in the WOTS chain view).
  const activeLeafNode = addMeshNode({
    id: `tree-leaf-${rootKindResolved}-${layerIndex ?? 'L'}-${treeIndex ?? 'T'}-${treeSeed ?? 0}`,
    title: leafTitle,
    meta: leafMeta + (truncated > 0 ? ` (Real tree has 2^${realDepth} leaves; only ${1 << visibleDepth} drawn here.)` : ''),
    kind: leafKind,
    zoomable: leafKind === 'xmss',
    color,
    layerIndex,
    treeIndex,
    activeLeafIdx: leafIdx,
    seed: 60 + (treeSeed ?? 0),
    baseScale: isExpandedLevel(visibleDepth) ? 0.55 : 0.9,
    position: positions[visibleDepth][leafIdx],
  });

  // Truncation indicator handled BELOW in the edge loop: the single edge
  // between the active mid at level visibleDepth-1 and the active leaf is
  // rendered DASHED, representing the (realDepth − visibleDepth) compressed
  // levels. That dashed edge is clickable to reveal one more level.

  // Active-path internal nodes (level 1..visibleDepth-1): also individual meshes
  // so they highlight cleanly with the polyline.
  const internalActiveNodes = [];
  for (let level = 1; level < visibleDepth; level += 1) {
    const idx = activeIdxByLevel[level];
    const pos = positions[level][idx];
    const node = addMeshNode({
      id: `tree-mid-${rootKindResolved}-${layerIndex ?? 'L'}-${treeIndex ?? 'T'}-${treeSeed ?? 0}-${level}`,
      title: `${rootTitle} · level ${level}/${visibleDepth}`,
      meta: `Internal Merkle node along the auth path (real tree depth ${realDepth}).`,
      kind: rootKind === 'fors-root' ? 'fors-root' : 'xmss',
      zoomable: false,
      color,
      layerIndex,
      treeIndex,
      seed: 70 + (treeSeed ?? 0) * 10 + level,
      baseScale: isExpandedLevel(level) ? expandedScale : 0.78,
      position: pos,
    });
    internalActiveNodes.push(node);
  }

  // First/last leaf index annotations — small labels at the corners of the
  // leaf row so the user reads "leaves are indexed 1 … 2^realDepth".
  if (leafCount >= 2) {
    const leftPos = positions[visibleDepth][0];
    const rightPos = positions[visibleDepth][leafCount - 1];
    const firstLabel = {
      kind: 'sigcell',
      embedTitle: `idx 1`,
      embedInfo: rootKind === 'fors-root' ? 'first sk' : 'first WOTS+ pk',
      position: new Vector3(leftPos.x - 0.05, leftPos.y - 0.18, leftPos.z),
    };
    const lastLabel = {
      kind: 'sigcell',
      embedTitle: `idx 2^${realDepth}`,
      embedInfo: rootKind === 'fors-root' ? 'last sk' : 'last WOTS+ pk',
      position: new Vector3(rightPos.x + 0.05, rightPos.y - 0.18, rightPos.z),
    };
    makeNodeLabel(firstLabel);
    makeNodeLabel(lastLabel);
    labelOnlyNodes.push(firstLabel, lastLabel);
  }

  // Off-path nodes split into TWO InstancedMeshes per tree:
  //   1. internal nodes (levels 1..visibleDepth-1)  → spheres   (circles per FIPS Fig 1)
  //   2. leaf-row off-path siblings (level visibleDepth) → boxes for XMSS (WOTS+ pks),
  //      octahedra for FORS (secret values).
  // Each instance carries info in `userData.ghostInfo[i]` so the raycaster's
  // instanceId hit lookup gives the user a hover description.
  const isFors = rootKind === 'fors-root';
  const internalGhosts = [];
  const leafGhosts = [];
  for (let level = 1; level < visibleDepth; level += 1) {
    const activeIdxAtLevel = activeIdxByLevel[level];
    for (let i = 0; i < positions[level].length; i += 1) {
      if (i === activeIdxAtLevel) continue;
      internalGhosts.push({ position: positions[level][i], level, indexAtLevel: i });
    }
  }
  for (let i = 0; i < positions[visibleDepth].length; i += 1) {
    if (i === activeIdxByLevel[visibleDepth]) continue;
    leafGhosts.push({ position: positions[visibleDepth][i], level: visibleDepth, indexAtLevel: i });
  }
  const treeKindLabel = isFors ? `FORS t=${(treeIndex ?? 0) + 1}` : `XMSS d=${layerIndex ?? 0}`;
  const treeRealDepth = realDepth;
  const buildInstanced = (entries, geom) => {
    if (!entries.length) return;
    const inst = new InstancedMesh(geom, ghostMaterialFor(color), entries.length);
    const m = new Matrix4();
    const q = new Quaternion();
    const s = new Vector3(1, 1, 1);
    entries.forEach((entry, i) => {
      // Thin per-instance scale at expanded levels.
      const scl = isExpandedLevel(entry.level) ? expandedScale : 1;
      s.set(scl, scl, scl);
      m.compose(entry.position, q, s);
      inst.setMatrixAt(i, m);
    });
    inst.instanceMatrix.needsUpdate = true;
    inst.userData.ghostInfo = entries.map((entry) => {
      const isLeaf = entry.level === visibleDepth;
      const realLevel = treeRealDepth - (visibleDepth - entry.level);
      const labelKindWord = isLeaf
        ? (isFors ? 'FORS leaf' : 'WOTS+ pk (= XMSS leaf)')
        : 'interior Merkle node';
      return {
        title: `${treeKindLabel} · ${labelKindWord}`,
        meta: isLeaf
          ? (isFors
              ? `Off-path FORS leaf in ${treeKindLabel}. Tree height a=${treeRealDepth}; this leaf is one of 2^${treeRealDepth} secret values, not opened by this signature.`
              : `Sibling WOTS+ public key — one of 2^${treeRealDepth} leaves of ${treeKindLabel}. Per FIPS 205 §3, the leaves of an XMSS tree ARE WOTS+ pks (squares in Fig 1).`)
          : `Off-path interior Merkle node at level ${entry.level}/${visibleDepth} (real depth ${treeRealDepth}). Hashed pair of two children — circle in FIPS Fig 1.`,
        kind: isLeaf ? (isFors ? 'fors' : 'xmss-leaf') : 'merkle-internal',
      };
    });
    inst.userData.hoverable = true;
    ghostMeshes.push(inst);
    selectable.push(inst); // raycaster needs to see this for hover
    world.add(inst);
  };
  // Ghost siblings share the family shape: FORS internal/leaf → small square;
  // XMSS internal → small circle; XMSS leaf → small triangle (the WOTS+ pk).
  const internalGhostGeom = isFors ? forsSquareSmallGeometry : xmssCircleSmallGeometry;
  const leafGhostGeom = isFors ? forsSquareSmallGeometry : wotsTriangleSmallGeometry;
  buildInstanced(internalGhosts, internalGhostGeom);
  buildInstanced(leafGhosts, leafGhostGeom);

  // Edges: every parent → both children. The single edge between the active
  // mid at level visibleDepth-1 and the active leaf is rendered dashed iff
  // truncated > 0 — it visually carries the (realDepth − visibleDepth)
  // compressed levels and is the click target for the "expand by one level"
  // affordance.
  const merkleMeta = isFors ? EDGE_META.merkle_fors : EDGE_META.merkle_xmss;
  for (let level = 0; level < visibleDepth; level += 1) {
    for (let i = 0; i < positions[level].length; i += 1) {
      const parent = positions[level][i];
      const left = positions[level + 1][2 * i];
      const right = positions[level + 1][2 * i + 1];
      const onPathParent = activeIdxByLevel[level] === i;
      const isLastLevel = level === visibleDepth - 1;
      const handleChild = (childPos, childIdx) => {
        const onPathChild = activeIdxByLevel[level + 1] === childIdx;
        const isActiveEdge = onPathParent && onPathChild;
        // Truncation dots ONLY on the active path's last edge. Off-path edges
        // stay solid even at the truncated level — drawing dots on every
        // sibling produced a wall of circles that read as a row of nodes.
        if (isLastLevel && truncated > 0 && isActiveEdge) {
          dashedEdgePairs.push([
            { position: parent },
            { position: childPos },
            { treeKey, truncated, realDepth, visibleDepth, kind: rootKindResolved },
          ]);
          return;
        }
        if (isActiveEdge) {
          edgePairs.push([{ position: parent }, { position: childPos }]);
          edgeMeta.push(merkleMeta);
        } else {
          ghostEdgePairs.push([{ position: parent }, { position: childPos }]);
          ghostEdgeMeta.push(merkleMeta);
        }
      };
      handleChild(left, 2 * i);
      handleChild(right, 2 * i + 1);
    }
  }

  return { rootNode, activeLeafNode, internalActiveNodes, activePath, visibleDepth, realDepth, truncated };
}

const routeLineMaterial = new LineBasicMaterial({ color: palette.path, transparent: true, opacity: 0.95 });
const pulse = new Mesh(
  new SphereGeometry(0.066, 18, 10),
  new MeshBasicMaterial({ color: palette.path, transparent: true, opacity: 0.95 }),
);
world.add(pulse);

function hashNoise(index, seed = 0) {
  const v = Math.sin(index * 12.9898 + seed * 78.233) * 43758.5453;
  return v - Math.floor(v);
}

function messageHex(seed) {
  const a = Math.floor(hashNoise(seed, 1) * 0xffffffff).toString(16).padStart(8, '0');
  const b = Math.floor(hashNoise(seed, 2) * 0xffffffff).toString(16).padStart(8, '0');
  return `0x${a}${b}…${variant().label.toLowerCase().replace(/[^a-z0-9]/g, '')}`;
}

function variant() {
  return params[state.variantKey];
}

function securityAtBudget(v, exponent) {
  const keys = Object.keys(v.sec).map(Number).sort((a, b) => a - b);
  if (exponent <= keys[0]) return v.sec[keys[0]];
  if (exponent >= keys.at(-1)) return v.sec[keys.at(-1)];
  for (let i = 0; i < keys.length - 1; i += 1) {
    const lo = keys[i];
    const hi = keys[i + 1];
    if (exponent >= lo && exponent <= hi) {
      const t = (exponent - lo) / (hi - lo);
      return v.sec[lo] + (v.sec[hi] - v.sec[lo]) * t;
    }
  }
  return 128;
}

function materialFor(color, kind) {
  const c = color instanceof Color ? color : new Color(color);
  // 2D mode — flat shaded, no specular / emissive. Double-sided so flat geos
  // remain visible regardless of camera flip.
  return new MeshBasicMaterial({ color: c, transparent: true, opacity: 0.95, side: DoubleSide });
}

function clearModel() {
  meshNodes.forEach((node) => {
    world.remove(node.mesh);
    disposeNodeLabel(node);
  });
  leafNodes.forEach((node) => disposeNodeLabel(node));
  labelOnlyNodes.forEach((node) => disposeNodeLabel(node));
  ghostMeshes.forEach((mesh) => world.remove(mesh));
  allNodes.length = 0;
  meshNodes.length = 0;
  leafNodes.length = 0;
  labelOnlyNodes.length = 0;
  edgePairs.length = 0;
  edgeMeta.length = 0;
  ghostMeshes.length = 0;
  ghostEdgePairs.length = 0;
  ghostEdgeMeta.length = 0;
  dashedEdgePairs.length = 0;
  ghostDashedEdgePairs.length = 0;
  selectable.length = 0;
  if (edgeLines) world.remove(edgeLines);
  if (ghostEdgeLines) world.remove(ghostEdgeLines);
  if (routeLine) world.remove(routeLine);
  edgeLines = null;
  ghostEdgeLines = null;
  routeLine = null;
  currentRoot = null;
}


function deriveEmbedText(node) {
  // Only label the structurally meaningful nodes — tree roots, active leaves,
  // FORS pk, WOTS+ bridges, pkRoot. Internal active-path nodes (`tree-mid-*`)
  // and instanced ghost nodes are unlabelled to keep the scene readable.
  if (node.embedTitle !== undefined || node.embedInfo !== undefined) return;
  const v = variant();
  const subtreeHeight = Math.floor(v.h / v.d);
  if (node.kind === 'fors-pk') {
    node.embedTitle = 'FORS pk';
    node.embedInfo = `T_k · k=${v.k}`;
    return;
  }
  if (node.kind === 'wots' && node.activeBridge) {
    node.embedTitle = `WOTS+ d=${node.layerIndex}`;
    node.embedInfo = `l=${v.l} · w=${v.w}`;
    return;
  }
  if (node.id?.startsWith('tree-root-')) {
    if (node.kind === 'root') {
      node.embedTitle = 'pkRoot';
      node.embedInfo = `n=${v.n}B · h=${v.h}, d=${v.d}`;
    } else if (node.kind === 'fors-root') {
      node.embedTitle = `FORS root t=${(node.treeIndex ?? 0) + 1}`;
      node.embedInfo = `a=${v.a}`;
    } else if (node.kind === 'xmss') {
      node.embedTitle = `XMSS d=${node.layerIndex} root`;
      node.embedInfo = `h/d=${subtreeHeight}`;
    }
    return;
  }
  if (node.id?.startsWith('tree-leaf-')) {
    if (node.kind === 'fors') {
      const t = node.treeIndex ?? 0;
      node.embedTitle = `FORS t=${t + 1}${node.activeLeafIdx !== undefined ? ` · idx=${node.activeLeafIdx}` : ''}`;
      node.embedInfo = `1 of 2^${v.a} leaves`;
    } else if (node.kind === 'xmss') {
      node.embedTitle = `XMSS d=${node.layerIndex} leaf${node.activeLeafIdx !== undefined ? ` · idx=${node.activeLeafIdx}` : ''}`;
      node.embedInfo = `1 of 2^${subtreeHeight}`;
    }
  }
}

function addMeshNode(node) {
  allNodes.push(node);
  const geom = geometryForNode(node);
  const mesh = new Mesh(geom, materialFor(node.color, node.kind));
  mesh.position.copy(node.position);
  mesh.userData.node = node;
  // 2D view: shapes face the camera by default, no random rotation.
  node.mesh = mesh;
  meshNodes.push(node);
  selectable.push(mesh);
  world.add(mesh);
  deriveEmbedText(node);
  makeNodeLabel(node);
  return node;
}

function addLeafNode(node) {
  allNodes.push(node);
  leafNodes.push(node);
  deriveEmbedText(node);
  makeNodeLabel(node);
  return node;
}

function updateNodeLabels() {
  if (!meshNodes.length && !leafNodes.length) return;
  const halfW = window.innerWidth * 0.5;
  const halfH = window.innerHeight * 0.5;
  const project = (node) => {
    if (!node.labelEl) return;
    const worldPos = node.mesh ? node.mesh.position : node.position;
    _labelProj.copy(worldPos).applyMatrix4(world.matrixWorld).project(camera);
    if (_labelProj.z >= 1 || _labelProj.z <= -1) {
      node.labelEl.style.display = 'none';
      return;
    }
    const x = _labelProj.x * halfW + halfW;
    const y = -_labelProj.y * halfH + halfH;
    node.labelEl.style.transform = `translate(${x}px, ${y}px) translate(-50%, -100%)`;
    if (node.labelEl.style.display === 'none') node.labelEl.style.display = 'block';
  };
  meshNodes.forEach(project);
  // Leaf-instance / annotation positions live on `node.position` (no per-node mesh).
  const projectByPos = (node) => {
    if (!node.labelEl) return;
    _labelProj.copy(node.position).applyMatrix4(world.matrixWorld).project(camera);
    if (_labelProj.z >= 1 || _labelProj.z <= -1) {
      node.labelEl.style.display = 'none';
      return;
    }
    const x = _labelProj.x * halfW + halfW;
    const y = -_labelProj.y * halfH + halfH;
    node.labelEl.style.transform = `translate(${x}px, ${y}px) translate(-50%, -100%)`;
    if (node.labelEl.style.display === 'none') node.labelEl.style.display = 'block';
  };
  leafNodes.forEach(projectByPos);
  labelOnlyNodes.forEach(projectByPos);
}

function connectLevels(levels) {
  for (let level = 0; level < levels.length - 1; level += 1) {
    levels[level + 1].forEach((child, i) => {
      const parentIndex = Math.min(levels[level].length - 1, Math.floor((i * levels[level].length) / levels[level + 1].length));
      edgePairs.push([levels[level][parentIndex], child]);
    });
  }
}

function nearestNode(nodes, position, seed = 0) {
  return nodes.reduce((best, node, index) => {
    const jitter = hashNoise(index, seed) * 0.18;
    const distance = node.position.distanceTo(position) + jitter;
    return distance < best.distance ? { node, distance } : best;
  }, { node: nodes[0], distance: Infinity }).node;
}

function makeTier(count, y, spread, z, kind, label, color, seed, zoomable = true, extra = {}) {
  const nodes = [];
  for (let i = 0; i < count; i += 1) {
    const centered = i - (count - 1) / 2;
    const x = count === 1 ? 0 : (centered / Math.max(1, (count - 1) / 2)) * spread * 0.5;
    const wobble = count === 1 ? 0 : (hashNoise(i, seed) - 0.5) * 0.34;
    nodes.push(addMeshNode({
      id: `${kind}-${seed}-${i}`,
      title: count === 1 ? label : `${label} ${i + 1}`,
      meta: extra.meta ?? (kind === 'xmss' ? 'Double-click to inspect this XMSS subtree.' : 'Double-click to inspect this layer.'),
      kind,
      zoomable,
      seed: seed * 31 + i,
      color,
      baseScale: kind === 'root' ? 1.12 : 1,
      position: new Vector3(x, y, z + wobble),
      ...extra,
    }));
  }
  return nodes;
}

// Visible-depth caps. Real Merkle trees can be h/d=22 deep (SLH-DSA) or a=24
// (FORS for SLH); we draw a complete binary tree up to these caps and visualise
// the truncated remainder as a fog cloud below the leaves.
const VISIBLE_XMSS_DEPTH = 6; // 64 leaves
const VISIBLE_FORS_DEPTH = 4; // 16 leaves

// Hypertree: k FORS trees fan into 1 FORS pk, then for each of d layers a
// single WOTS+ signs the input below and produces the active leaf of an XMSS
// Merkle tree drawn truncated to VISIBLE_XMSS_DEPTH.
//
// Verifier correspondence:
//   SPHINCs-C7Asm.sol:88-165, SPHINCs-C12Asm.sol:130-211,
//   SLH-DSA-keccak-128-24verifier.sol:76-188, jardin_spx_signer.py:258-299.
function buildHypertree() {
  const v = variant();
  const subtreeHeight = Math.floor(v.h / v.d);
  const forsVisible = Math.min(VISIBLE_FORS_DEPTH, v.a);
  const xmssVisible = Math.min(VISIBLE_XMSS_DEPTH, subtreeHeight);

  // Vertical layout. FORS lives in y < 0, hypertree in y > 0; FORS pk at y≈0.
  // Compact spacing — keeps the signature bar + formula on-screen above
  // the bottom HUD overlays.
  const FORS_ROOT_Y = -1.1;
  const FORS_LEAF_Y = -4.9;
  const FORS_PK_Y = -0.3;

  const layerHeight = Math.min(2.2, 10 / Math.max(2, v.d));
  const xmssRootY = (i) => FORS_PK_Y + 1.0 + (i + 1) * layerHeight;
  const xmssLeafYBase = (i) => xmssRootY(i) - layerHeight + 0.55;
  const wotsY = (i) => xmssLeafYBase(i) - 0.45;

  // ── k FORS trees ──────────────────────────────────────────────────────
  const forsCount = Math.min(v.k, 8);
  const forsSpread = 11.0;
  const forsTreeWidth = Math.min(1.6, forsSpread / Math.max(1, forsCount + 1));
  const forsTrees = [];
  const forsActiveLeafX = []; // actual world-x of each tree's selected leaf
  const forsActiveLeafIdx = []; // visualised leaf index per tree (in [0, 2^visibleDepth))
  for (let t = 0; t < forsCount; t += 1) {
    const centered = forsCount === 1 ? 0 : (t / (forsCount - 1) - 0.5);
    const x = centered * forsSpread;
    const activeLeaf = Math.floor(hashNoise(state.routeSeed, 200 + t) * (1 << forsVisible));
    forsActiveLeafIdx.push(activeLeaf);
    const tree = buildBinaryMerkleTree({
      rootPos: new Vector3(x, FORS_ROOT_Y, 0),
      visibleDepth: forsVisible,
      realDepth: v.a,
      width: forsTreeWidth,
      height: FORS_ROOT_Y - FORS_LEAF_Y,
      color: palette.fors,
      activeLeafIdx: activeLeaf,
      rootKind: 'fors-root',
      rootZoomable: true,
      rootTitle: `FORS root t=${t + 1}`,
      rootMeta: `Root of FORS tree ${t + 1} of k=${v.k} (height a=${v.a}). One of T_k's k inputs.`,
      leafKind: 'fors',
      leafTitle: `FORS leaf t=${t + 1}`,
      leafMeta: `FORS leaf = F(PK.seed, ADRS, sk_${t},${t}) where sk is the revealed secret value at index base_2b(md, a=${v.a}, k=${v.k})[${t}] in tree ${t + 1}. F is a tweakable hash on a single n-byte input (FIPS 205 §8.2 / Alg 15 line 5). Distinct from H, which combines two children at interior levels.`,
      treeIndex: t,
      treeSeed: t,
    });
    forsTrees.push(tree);
    forsActiveLeafX.push(tree.activeLeafNode.position.x);
  }

  // ── FORS signature composition row (bottom layer) ─────────────────────
  // Visualises the byte layout of the FORS signature per FIPS 205 §8.3:
  //   SIG_FORS = sk_0 ‖ AUTH_0 ‖ sk_1 ‖ AUTH_1 ‖ … ‖ sk_{k−1} ‖ AUTH_{k−1}
  // Each cell box carries its own hover info so the side panel shows
  // sk[n]/auth[a·n] details, not the unrelated Merkle-edge meta upstream.
  {
    const sigBarY = FORS_LEAF_Y - 1.05;
    const cellPadding = 0.1;
    const cellWidth = Math.max(0.9, (forsSpread / Math.max(1, forsCount)) - cellPadding);
    for (let t = 0; t < forsCount; t += 1) {
      const centered = forsCount === 1 ? 0 : (t / (forsCount - 1) - 0.5);
      const cx = centered * forsSpread;
      const skLeafIdx = Math.floor(hashNoise(state.routeSeed, 200 + t) * (1 << Math.min(VISIBLE_FORS_DEPTH, v.a)));

      // Auth-path body (a × n bytes)
      const body = new Mesh(
        new BoxGeometry(cellWidth, 0.18, 0.04),
        new MeshBasicMaterial({ color: 0x61d6ff, transparent: true, opacity: 0.5 }),
      );
      body.position.set(cx, sigBarY, 0);
      body.userData.cellInfo = {
        kind: 'sigcell',
        title: `FORS auth path · tree t=${t + 1}`,
        meta: `${v.a} × n = ${v.a}·${v.n} = ${v.a * v.n} B authentication-path siblings for FORS tree ${t + 1}. Each is one Merkle-tree sibling on the path from the revealed leaf up to the tree's root. Used by fors_pkFromSig to reconstruct root_${t} via the H tweakable hash. (FIPS 205 §8.4 Alg 17 lines 8–18.)`,
      };
      ghostMeshes.push(body);
      selectable.push(body);
      world.add(body);

      // sk byte (n bytes) — highlighted at the cell's left edge.
      const skWidth = cellWidth / (v.a + 1);
      const sk = new Mesh(
        new BoxGeometry(skWidth * 1.15, 0.26, 0.06),
        new MeshBasicMaterial({ color: 0xffcf8c, transparent: true, opacity: 0.95 }),
      );
      sk.position.set(cx - cellWidth / 2 + skWidth / 2, sigBarY, 0);
      sk.userData.cellInfo = {
        kind: 'sigcell',
        title: `FORS sk · tree t=${t + 1}`,
        meta: `sk[n=${v.n} B] — the revealed FORS secret value for tree ${t + 1}. Its index inside the tree is base_2b(md, a=${v.a}, k=${v.k})[${t}] (one of 2^${v.a} possible positions). When verifying, F(PK.seed, ADRS, sk) reproduces the leaf of tree ${t + 1}. (FIPS 205 §8.3 Alg 16 line 4.)`,
      };
      ghostMeshes.push(sk);
      selectable.push(sk);
      world.add(sk);

      // Connector from the selected FORS leaf above (NOT the tree centre) to
      // the sk box in this cell — visualises "this leaf's sk goes into the
      // signature here".
      const skX = cx - cellWidth / 2 + skWidth / 2;
      const leafX = forsActiveLeafX[t] ?? cx;
      const connGeom = new BufferGeometry();
      connGeom.setAttribute('position', new BufferAttribute(new Float32Array([
        leafX, FORS_LEAF_Y - 0.05, 0,
        skX, sigBarY + 0.18, 0,
      ]), 3));
      const conn = new LineSegments(
        connGeom,
        new LineBasicMaterial({ color: 0xffcf8c, transparent: true, opacity: 0.55 }),
      );
      ghostMeshes.push(conn);
      world.add(conn);

      // Per-cell label embedded on the bar — includes the active leaf index.
      const idx = forsActiveLeafIdx[t] ?? 0;
      const cellLabel = {
        kind: 'sigcell',
        embedTitle: `FORS t=${t + 1} · idx=${idx}`,
        embedInfo: `sk[n=${v.n}B] ‖ auth[${v.a}·n]`,
        position: new Vector3(cx, sigBarY + 0.32, 0),
      };
      makeNodeLabel(cellLabel);
      labelOnlyNodes.push(cellLabel);
    }
    // In-plane formula label below the cells (camera is centred on the scene
    // mid-Y so it always sits in the visible area).
    const sigLabel = {
      kind: 'sigformula',
      embedTitle: `FORS signature  =  ${v.k} × (sk[n] ‖ auth[${v.a}·n])`,
      embedInfo: `k·(a+1)·n  =  ${v.k}·${v.a + 1}·${v.n}  =  ${v.k * (v.a + 1) * v.n} bytes`,
      position: new Vector3(0, sigBarY - 0.55, 0),
    };
    makeNodeLabel(sigLabel);
    labelOnlyNodes.push(sigLabel);
  }

  // ── FORS pk = T_k(roots) ──────────────────────────────────────────────
  const forsPk = addMeshNode({
    id: 'fors-pk',
    title: 'FORS pk',
    meta: `FORS public key = T_k(PK.seed, FORS_ROOTS-ADRS, root_0 ‖ … ‖ root_${v.k - 1}). Signed by WOTS+ at d=0. (FIPS 205 Alg. 17.)`,
    kind: 'fors-pk',
    zoomable: true,
    seed: 75,
    layerIndex: -1,
    color: palette.fors,
    baseScale: 1.22,
    position: new Vector3(0, FORS_PK_Y, 0),
  });
  // T_k fan-in: every FORS root edges into the single FORS pk.
  forsTrees.forEach((tree) => {
    edgePairs.push([forsPk, tree.rootNode]);
    edgeMeta.push(EDGE_META.tk_fors);
  });

  // ── d XMSS layers, each prefaced by one WOTS+ ─────────────────────────
  // Subtle horizontal divider lines between layers so the d=2 / d=5 stack
  // reads as discrete layers. Every layer carries a "d=N" label on the
  // right side, hugging the divider line.
  const subtreeHeightForLabel = subtreeHeight;
  for (let i = 0; i <= v.d; i += 1) {
    const dividerY = (i === 0 ? FORS_PK_Y + 0.55 : xmssRootY(i - 1) + 0.18);
    const dividerWidth = Math.max(8, 2.5 + xmssVisible * 0.9) * 0.75;
    const divGeom = new BufferGeometry();
    divGeom.setAttribute('position', new BufferAttribute(new Float32Array([
      -dividerWidth, dividerY, 0,
      dividerWidth, dividerY, 0,
    ]), 3));
    const divLine = new LineSegments(divGeom, new LineBasicMaterial({ color: 0x2c3530, transparent: true, opacity: 0.45 }));
    ghostMeshes.push(divLine);
    world.add(divLine);
  }
  // Layer "d=N" labels — one per layer, sitting at the layer's vertical centre
  // on the right side of the tree, so each XMSS layer reads as labelled.
  for (let i = 0; i < v.d; i += 1) {
    const labelY = (xmssRootY(i) + (i === 0 ? FORS_PK_Y + 0.55 : xmssRootY(i - 1))) * 0.5;
    const labelX = Math.max(8, 2.5 + xmssVisible * 0.9) * 0.75 + 0.4;
    const annotation = {
      kind: 'layer-divider',
      embedTitle: `d = ${i}`,
      embedInfo: `XMSS layer · h/d=${subtreeHeightForLabel}`,
      position: new Vector3(labelX, labelY, 0),
    };
    makeNodeLabel(annotation);
    labelOnlyNodes.push(annotation);
  }
  // pkRoot label at the very top.
  const topRootLabel = {
    kind: 'layer-divider',
    embedTitle: 'pkRoot',
    embedInfo: `XMSS d=${v.d - 1} root`,
    position: new Vector3(Math.max(8, 2.5 + xmssVisible * 0.9) * 0.75 + 0.4, xmssRootY(v.d - 1) + 0.4, 0),
  };
  makeNodeLabel(topRootLabel);
  labelOnlyNodes.push(topRootLabel);

  let prevOutput = forsPk;
  let topRoot = null;
  for (let i = 0; i < v.d; i += 1) {
    const isTop = i === v.d - 1;

    const wots = addMeshNode({
      id: `wots-bridge-${i}`,
      title: `WOTS+ d=${i}`,
      meta: `Single WOTS+ at d=${i} signing ${i === 0 ? 'FORS pk' : `XMSS d=${i - 1} root`}. l=${v.l} chains × w=${v.w} (chain length w-1=${v.w - 1}); T_l(endpoints) = active leaf of XMSS d=${i}.`,
      kind: 'wots',
      zoomable: true,
      activeBridge: true,
      sourceNode: prevOutput,
      layerIndex: i,
      seed: 500 + i,
      color: palette.wots,
      baseScale: 1.0,
      position: new Vector3(0, wotsY(i), 0.4),
    });
    edgePairs.push([prevOutput, wots]);
    edgeMeta.push(EDGE_META.wots_input);

    const activeLeaf = Math.floor(hashNoise(state.routeSeed, 700 + i) * (1 << xmssVisible));
    const xmssTree = buildBinaryMerkleTree({
      rootPos: new Vector3(0, xmssRootY(i), 0),
      visibleDepth: xmssVisible,
      realDepth: subtreeHeight,
      width: Math.max(6, 2.5 + xmssVisible * 0.9),
      height: xmssRootY(i) - xmssLeafYBase(i),
      color: palette.xmss,
      activeLeafIdx: activeLeaf,
      rootKind: 'xmss',
      rootKindIfTop: 'root',
      rootZoomable: !isTop || v.d === 1,
      rootTitle: isTop ? `pkRoot · XMSS d=${i} root` : `XMSS d=${i} root`,
      rootMeta: isTop
        ? 'pkRoot — root of the top XMSS subtree. Verifier accepts iff the reconstructed root equals this 16-byte value.'
        : `Root of XMSS d=${i} (subtree height h/d=${subtreeHeight}). Becomes the message signed by WOTS+ at d=${i + 1}.`,
      leafKind: 'xmss',
      leafTitle: `XMSS d=${i} active leaf`,
      leafMeta: `Active leaf of XMSS d=${i}. Equal to the WOTS+ pk that wots_pkFromSig produced from the WOTS+ signature below.`,
      layerIndex: i,
      isTop,
      treeSeed: 100 + i,
    });
    // WOTS+ pk = the active leaf of this layer's XMSS tree.
    edgePairs.push([wots, xmssTree.activeLeafNode]);
    edgeMeta.push(EDGE_META.wots_output);
    wots.targetNode = xmssTree.activeLeafNode;

    prevOutput = xmssTree.rootNode;
    if (isTop) topRoot = xmssTree.rootNode;
  }

  currentRoot = topRoot ?? forsPk;
}

function buildXmssSubtree(parent) {
  const v = variant();
  const seed = parent.seed ?? state.view.seed;
  const layerIndex = parent.layerIndex ?? state.view.layerIndex ?? 0;
  const subtreeHeight = Math.floor(v.h / v.d);
  const levels = [];
  levels.push(makeTier(1, 3.6, 0, 0, 'root', parent.title, palette.root, seed, false, {
    layerIndex,
    meta: `Root of XMSS d=${layerIndex} (subtree height h/d=${subtreeHeight}). Reconstructed by hashing the active WOTS+ pk up the Merkle tree using the auth path siblings.`,
  }));
  levels.push(makeTier(2, 2.1, 3.2, -0.22, 'xmss', 'auth node', palette.xmss, seed + 1, true, {
    layerIndex,
    meta: `XMSS internal node H(PK.seed, ADRS, lnode ‖ rnode). One sibling at this level is part of the auth path.`,
  }));
  levels.push(makeTier(4, 0.7, 5.8, 0.24, 'xmss', 'auth node', palette.xmss, seed + 2, true, {
    layerIndex,
    meta: `XMSS internal node — one sibling at this level is included in the auth path.`,
  }));
  const leafCount = 8;
  const leaves = makeTier(leafCount, -0.88, 8.8, -0.18, 'wots-root', 'WOTS+ pk', palette.wots, seed + 3, true, {
    layerIndex,
    meta: `WOTS+ public keys form the 2^(h/d)=${2 ** subtreeHeight > 999 ? `2^${subtreeHeight}` : 2 ** subtreeHeight} leaves of XMSS d=${layerIndex}. Per signature exactly one is the active leaf.`,
  });
  levels.push(leaves);
  connectLevels(levels);

  // Mark a single leaf as the active one (idx_leaf within this subtree).
  const activeLeafIdx = Math.floor(hashNoise(seed + state.routeSeed, 911) * leafCount);
  leaves.forEach((leaf, i) => {
    leaf.activeLeaf = i === activeLeafIdx;
    if (!leaf.activeLeaf) {
      leaf.title = `WOTS+ pk (sibling)`;
      leaf.meta = `Sibling WOTS+ public key at this XMSS leaf — not the active leaf for this signature, just a member of the Merkle tree.`;
    } else {
      leaf.title = 'WOTS+ pk (active)';
      leaf.meta = `Active WOTS+ pk at this XMSS leaf. Reconstructed by wots_pkFromSig from the WOTS+ signature and the lower-layer message.`;
    }
  });

  // Single signed input (FORS pk for d=0, lower-layer XMSS root otherwise) and
  // a single WOTS+ bridge connecting it to the ACTIVE leaf only.
  const sourceLabel = layerIndex === 0 ? 'FORS pk' : `XMSS d=${layerIndex - 1} root`;
  const signedInput = addMeshNode({
    id: `xmss-source-${seed}`,
    title: sourceLabel,
    meta: layerIndex === 0
      ? 'FORS public key is the message signed by WOTS+ at d=0. Single value (output of T_k).'
      : `Single XMSS d=${layerIndex - 1} root — the message signed by WOTS+ at d=${layerIndex}.`,
    kind: layerIndex === 0 ? 'fors-pk' : 'root',
    zoomable: false,
    seed: seed + 9,
    layerIndex: layerIndex - 1,
    color: layerIndex === 0 ? palette.fors : palette.root,
    baseScale: 1.06,
    position: new Vector3(0, -2.65, 0.32),
  });

  const activeLeaf = leaves[activeLeafIdx];
  const bridgePos = signedInput.position.clone().lerp(activeLeaf.position, 0.55);
  bridgePos.z += 0.45;
  const bridge = addMeshNode({
    id: `xmss-wots-${seed}`,
    title: `WOTS+ d=${layerIndex}`,
    meta: `Single WOTS+ instance verifying the signature: completes l=${v.l} chains to position w-1=${v.w - 1}, T_l-compresses to the active WOTS+ pk (one leaf of this XMSS subtree).`,
    kind: 'wots',
    zoomable: true,
    activeBridge: true,
    layerIndex,
    sourceNode: signedInput,
    targetNode: activeLeaf,
    seed: seed * 100 + activeLeafIdx,
    color: palette.wots,
    baseScale: 1.05,
    position: bridgePos,
  });
  edgePairs.push([signedInput, bridge]);
  edgePairs.push([bridge, activeLeaf]);
  currentRoot = levels[0][0];
}

function buildForsForest(parent) {
  const v = variant();
  const seed = parent.seed ?? state.view.seed;
  const levels = [];
  levels.push(makeTier(1, 3.45, 0, 0, 'root', parent.title, palette.root, seed, false, {
    layerIndex: -1,
    meta: `FORS public key = T_k(PK.seed, FORSROOTS, root_0 ‖ … ‖ root_{k-1}). FIPS 205 Algorithm 17.`,
  }));
  levels.push(makeTier(Math.min(v.k, 6), 2.0, 6.8, -0.25, 'fors-root', 'FORS tree', palette.fors, seed + 1, true, {
    layerIndex: -1,
    meta: `One of k=${v.k} FORS trees, height a=${v.a}, 2^${v.a} leaves. Signature opens one leaf per tree.`,
  }));
  levels.push(makeTier(Math.min(v.k * 2, 12), 0.4, 9.2, 0.25, 'fors-root', 'FORS auth', palette.fors, seed + 2, true, {
    layerIndex: -1,
    meta: `Auth path node inside a FORS tree of height a=${v.a}.`,
  }));
  connectLevels(levels);

  const branches = levels.at(-1);
  branches.forEach((anchor, branch) => {
    for (let i = 0; i < 4; i += 1) {
      const node = addLeafNode({
        id: `fors-secret-${seed}-${branch}-${i}`,
        title: `secret leaf ${branch + 1}.${i + 1}`,
        meta: `FORS reveals the secret value at this leaf and an a=${v.a} step auth path.`,
        kind: 'fors',
        layerIndex: -1,
        treeIndex: branch,
        seed: seed * 100 + branch * 4 + i,
        color: palette.fors,
        position: new Vector3(
          anchor.position.x + (i - 1.5) * 0.16,
          -2.05 - hashNoise(i, seed) * 0.2,
          anchor.position.z + 0.62,
        ),
      });
      edgePairs.push([anchor, node]);
    }
  });
  currentRoot = levels[0][0];
}

function buildWotsChains(parent) {
  const v = variant();
  const seed = parent.seed ?? state.view.seed;
  const layerIndex = parent.layerIndex ?? state.view.layerIndex ?? 0;
  // We draw min(l, VISIBLE_WOTS_CHAINS) chains and indicate the truncation
  // (the remaining l − VISIBLE chains are represented by dotted continuation
  // marks on the right). All visible chains contribute equally to T_l → pk;
  // there is no "active" chain — every chain is used by wots_pkFromSig.
  const VISIBLE_WOTS_CHAINS = 12;
  const chainCount = Math.min(VISIBLE_WOTS_CHAINS, v.l);
  const truncatedChains = Math.max(0, v.l - chainCount);
  const stepCount = Math.max(2, Math.min(v.w - 1, 6));
  const root = addMeshNode({
    id: `wots-root-${seed}`,
    title: `WOTS+ pk d=${layerIndex}`,
    meta: `WOTS+ public key. ALL l=${v.l} chains contribute: pk = T_l(PK.seed, ADRS, ep_0 ‖ … ‖ ep_${v.l - 1}) where ep_i is the endpoint of chain i (each chain advanced from sig[i] to position w-1=${v.w - 1}). No chain is "selected" — every chain encodes log2(w) bits of the message digit and every endpoint is required. This pk equals one leaf of XMSS d=${layerIndex} above. (FIPS 205 §5 / Algorithms 6, 8.)`,
    kind: 'wots-pk',
    role: 'wots-pk',
    zoomable: false,
    seed,
    layerIndex,
    color: palette.wots,
    baseScale: 1.18,
    position: new Vector3(0, 2.85, 0),
  });
  const source = addMeshNode({
    id: `wots-source-${seed}`,
    title: layerIndex === 0 ? 'FORS pk' : `XMSS d=${layerIndex - 1} root`,
    meta: layerIndex === 0
      ? 'FORS public key feeds into WOTS+ at d=0 as the message being signed. base_w splits it into l digits, one per chain.'
      : `XMSS d=${layerIndex - 1} root is the message signed by WOTS+ at d=${layerIndex}. base_w splits it into l digits, one per chain.`,
    kind: layerIndex === 0 ? 'fors-root' : 'xmss',
    role: 'wots-source',
    zoomable: false,
    seed: seed + 17,
    layerIndex: layerIndex - 1,
    color: layerIndex === 0 ? palette.fors : palette.xmss,
    baseScale: 1.02,
    position: new Vector3(0, -2.65, 0),
  });
  currentRoot = root;
  const xStart = -5.4;
  const xStep = chainCount > 1 ? 10.8 / (chainCount - (truncatedChains > 0 ? 0 : 1)) : 0;
  for (let chain = 0; chain < chainCount; chain += 1) {
    const x = xStart + chain * xStep * 0.95;
    let previous = source;
    for (let step = 0; step < stepCount; step += 1) {
      const tt = (step + 1) / (stepCount + 1);
      const node = addMeshNode({
        id: `wots-${seed}-${chain}-${step}`,
        title: `chain ${chain + 1}/${v.l}, step ${step + 1}/${v.w - 1}`,
        meta: `One F-evaluation along WOTS+ chain ${chain + 1} (of l=${v.l} total): F(PK.seed, ADRS, x). Verifier advances this chain to position w-1=${v.w - 1}. ALL l chains do this in parallel; their endpoints are T_l-compressed into the WOTS+ pk above. FIPS 205 §5 / Algorithm 5.`,
        kind: 'wots',
        zoomable: false,
        layerIndex,
        chainIndex: chain,
        stepIndex: step,
        seed: seed * 1000 + chain * 10 + step,
        color: palette.wots,
        baseScale: 0.9,
        position: new Vector3(x, -2.65 + tt * 5.5, 0),
      });
      edgePairs.push([previous, node]);
      edgeMeta.push(EDGE_META.wots_chain_step);
      previous = node;
    }
    edgePairs.push([previous, root]);
    edgeMeta.push(EDGE_META.wots_compress);
  }
  // Chain-count truncation indicator: dotted continuation on the right plus a
  // small "+ N more chains" label.
  if (truncatedChains > 0) {
    const xRightmost = xStart + (chainCount - 1) * xStep * 0.95;
    const xTrail = xRightmost + xStep * 0.95;
    const yMid = -2.65 + 5.5 * 0.5;
    // Dashed connector indicating "more chains continue" — rendered via the
    // ghostDashed dots system for consistency with tree truncation.
    ghostDashedEdgePairs.push([
      { position: new Vector3(xRightmost + 0.5, yMid, 0) },
      { position: new Vector3(xTrail + 1.5, yMid, 0) },
    ]);
    const annotation = {
      kind: 'truncation',
      embedTitle: `+ ${truncatedChains} more chains`,
      embedInfo: `total l = ${v.l} (showing ${chainCount})`,
      position: new Vector3(xTrail + 0.8, yMid - 0.5, 0),
    };
    makeNodeLabel(annotation);
    labelOnlyNodes.push(annotation);
  }
  // "All l chains used" banner above the chains.
  const banner = {
    kind: 'sigformula',
    embedTitle: `All l = ${v.l} chains used by wots_pkFromSig`,
    embedInfo: `pk = T_l(seed, ADRS, ep_0 ‖ … ‖ ep_{l-1})`,
    position: new Vector3(0, 3.6, 0),
  };
  makeNodeLabel(banner);
  labelOnlyNodes.push(banner);
}

// Builds (or rebuilds) the small camera-anchored minimap that shows the full
// hypertree skeleton during drilldown views. Hidden when on the hypertree view
// (it would just duplicate what's on screen).
function rebuildMinimap() {
  while (minimapAnchor.children.length) {
    const c = minimapAnchor.children[0];
    minimapAnchor.remove(c);
  }
  if (state.view.type === 'hypertree') {
    minimapAnchor.visible = false;
    return;
  }
  minimapAnchor.visible = true;

  const v = variant();
  const layerSpacing = 1.6;
  const triBaseWidth = 1.8;
  const triHeight = 1.1;
  const subtreeHeightForLabel = Math.floor(v.h / v.d);

  const accent = new Color(v.color);
  const baseLineMat = new LineBasicMaterial({ color: 0x4a5b56, transparent: true, opacity: 0.55 });
  const accentLineMat = new LineBasicMaterial({ color: accent.getHex(), transparent: true, opacity: 0.95 });
  const dimMat = new LineBasicMaterial({ color: 0x4a5b56, transparent: true, opacity: 0.45 });
  const wotsLineMat = new LineBasicMaterial({ color: 0xf35f8f, transparent: true, opacity: 0.6 });

  const isHighlightedXmss = (i) => (state.view.type === 'xmss' || state.view.type === 'wots') && state.view.layerIndex === i;
  const isFors = state.view.type === 'fors';

  const triangleOutline = (cx, cy, base, height, mat) => {
    const geom = new BufferGeometry();
    geom.setAttribute('position', new BufferAttribute(new Float32Array([
      cx, cy + height / 2, 0,
      cx - base / 2, cy - height / 2, 0,
      cx + base / 2, cy - height / 2, 0,
      cx, cy + height / 2, 0,
    ]), 3));
    return new Line(geom, mat);
  };

  // d XMSS layers stacked vertically (top = pkRoot)
  const baseY = 0;
  for (let i = 0; i < v.d; i += 1) {
    const cy = baseY + i * layerSpacing;
    const tri = triangleOutline(0, cy, triBaseWidth, triHeight, isHighlightedXmss(i) ? accentLineMat : baseLineMat);
    minimapAnchor.add(tri);
    // small WOTS+ tick between layers
    if (i > 0) {
      const dotGeom = new BufferGeometry();
      dotGeom.setAttribute('position', new BufferAttribute(new Float32Array([
        0, cy - layerSpacing / 2 - 0.05, 0,
        0, cy - layerSpacing / 2 + 0.05, 0,
      ]), 3));
      const wotsLine = new LineSegments(dotGeom, wotsLineMat);
      minimapAnchor.add(wotsLine);
    }
  }

  // FORS pk dot below the bottom XMSS triangle
  const forsPkY = baseY - 1.0;
  const pkDot = new Mesh(
    new SphereGeometry(0.14, 10, 8),
    new MeshBasicMaterial({ color: 0x61d6ff, transparent: true, opacity: isFors ? 1 : 0.65 }),
  );
  pkDot.position.set(0, forsPkY, 0);
  minimapAnchor.add(pkDot);

  // k FORS trees fanned below the FORS pk
  const forsCount = Math.min(v.k, 6);
  const forsRowY = forsPkY - 1.4;
  const forsSpread = 4.5;
  const forsBase = 0.6;
  for (let t = 0; t < forsCount; t += 1) {
    const x = forsCount === 1 ? 0 : ((t / (forsCount - 1)) - 0.5) * forsSpread;
    const tri = triangleOutline(x, forsRowY, forsBase, 0.7, isFors ? accentLineMat : dimMat);
    minimapAnchor.add(tri);
    // T_k connector from FORS pk to each tree root
    const linkGeom = new BufferGeometry();
    linkGeom.setAttribute('position', new BufferAttribute(new Float32Array([
      0, forsPkY - 0.14, 0,
      x, forsRowY + 0.35, 0,
    ]), 3));
    const link = new LineSegments(linkGeom, isFors ? accentLineMat : dimMat);
    minimapAnchor.add(link);
  }

}

function rebuild() {
  clearModel();
  if (state.view.type === 'hypertree') buildHypertree();
  if (state.view.type === 'xmss') buildXmssSubtree(state.view.node);
  if (state.view.type === 'fors') buildForsForest(state.view.node);
  if (state.view.type === 'wots') buildWotsChains(state.view.node);
  rebuildMinimap();

  const edgeGeometry = new BufferGeometry();
  const edgePositions = new Float32Array(edgePairs.length * 2 * 3);
  edgePairs.forEach(([a, b], i) => {
    edgePositions.set(a.position.toArray(), i * 6);
    edgePositions.set(b.position.toArray(), i * 6 + 3);
  });
  edgeGeometry.setAttribute('position', new BufferAttribute(edgePositions, 3));
  // LineSegments: each consecutive pair of vertices is ONE independent segment.
  // (Plain `Line` would connect every vertex to the next, drawing spurious cross-
  // tree edges between consecutive edge pairs.)
  edgeLines = new LineSegments(edgeGeometry, new LineBasicMaterial({ color: 0x41504c, transparent: true, opacity: 0.26 }));
  edgeLines.userData.edgeMeta = edgeMeta;
  selectable.push(edgeLines);
  world.add(edgeLines);

  if (ghostEdgePairs.length) {
    const gGeom = new BufferGeometry();
    const gPos = new Float32Array(ghostEdgePairs.length * 2 * 3);
    ghostEdgePairs.forEach(([a, b], i) => {
      gPos.set(a.position.toArray(), i * 6);
      gPos.set(b.position.toArray(), i * 6 + 3);
    });
    gGeom.setAttribute('position', new BufferAttribute(gPos, 3));
    ghostEdgeLines = new LineSegments(gGeom, new LineBasicMaterial({ color: 0x2c3937, transparent: true, opacity: 0.18 }));
    ghostEdgeLines.userData.edgeMeta = ghostEdgeMeta;
    selectable.push(ghostEdgeLines);
    world.add(ghostEdgeLines);
  }

  // LineSegments2 + LineMaterial — Three.js's "fat line" path. Standard
  // LineBasicMaterial caps at 1px in WebGL, so any dash pattern reads as a
  // continuous hairline. LineMaterial draws actual triangle-strip lines with
  // pixel-precise width AND a working dashed mode.
  if (dashedEdgePairs.length) {
    const positions = [];
    const dashedMeta = [];
    dashedEdgePairs.forEach(([a, b, info]) => {
      positions.push(
        a.position.x, a.position.y, a.position.z,
        b.position.x, b.position.y, b.position.z,
      );
      dashedMeta.push(info ?? null);
    });
    const geom = new LineSegmentsGeometry();
    geom.setPositions(positions);
    const mat = new LineMaterial({
      color: 0xffcf8c,
      linewidth: 3,            // pixels (LineMaterial draws as triangles)
      dashed: true,
      dashSize: 0.18,          // world units along the line
      gapSize: 0.14,           // world units along the line
      transparent: false,
      // NO worldUnits: true — that would make linewidth=3 mean 3 world units
      // thick (~160 px) and the dashes get hidden inside an enormous bar.
      resolution: new Vector2(window.innerWidth, window.innerHeight),
    });
    const seg = new LineSegments2(geom, mat);
    seg.computeLineDistances();
    seg.userData.dashedMeta = dashedMeta;
    seg.userData.lineMaterial = mat; // pick up in resize() to update resolution
    ghostMeshes.push(seg);
    selectable.push(seg);
    world.add(seg);
  }

  routeGeometry = new BufferGeometry();
  routeLine = new LineSegments(routeGeometry, routeLineMaterial);
  world.add(routeLine);

  refreshRoute();
  updateInstances();
  updateHud();
  focusScene(false);
}

// Returns { highlights, polyline }. `highlights` is every node that gets the
// path-coloured tint (auth members + verification trace); `polyline` is the
// strict ordered sequence of nodes the route line draws through. They differ
// because k FORS leaves and k FORS roots are all auth members, but only one of
// each is on the linear verification polyline (which then converges through
// the single FORS pk and continues).
function routeNodes() {
  const v = variant();

  if (state.view.type === 'wots') {
    const source = meshNodes.find((node) => node.role === 'wots-source');
    const root = meshNodes.find((node) => node.role === 'wots-pk');
    const chainIndex = meshNodes.find((node) => node.kind === 'wots' && node.activeChain)?.chainIndex ?? 0;
    const chain = meshNodes
      .filter((node) => node.kind === 'wots' && node.chainIndex === chainIndex)
      .sort((a, b) => a.stepIndex - b.stepIndex);
    const seq = [source, ...chain, root].filter(Boolean);
    const segs = [];
    for (let i = 0; i + 1 < seq.length; i += 1) segs.push([seq[i], seq[i + 1]]);
    return { highlights: seq, segments: segs };
  }

  if (state.view.type === 'hypertree') {
    const highlights = [];
    const segments = []; // array of [fromNode, toNode] — each is one polyline segment

    // Indexes built from the unified tree-builder id prefixes.
    const treeRoots = new Map();
    const treeLeaves = new Map();
    const treeMids = new Map();
    meshNodes.forEach((n) => {
      const key = n.layerIndex >= 0 ? `xmss:${n.layerIndex}` : `fors:${n.treeIndex}`;
      if (n.id?.startsWith('tree-root-')) treeRoots.set(key, n);
      else if (n.id?.startsWith('tree-leaf-')) treeLeaves.set(key, n);
      else if (n.id?.startsWith('tree-mid-')) {
        if (!treeMids.has(key)) treeMids.set(key, []);
        treeMids.get(key).push(n);
      }
    });
    treeMids.forEach((arr) => arr.sort((a, b) => a.position.y - b.position.y));
    const forsPk = meshNodes.find((n) => n.kind === 'fors-pk');

    // ALL k FORS trees: highlight each tree's active path (leaf → mids → root)
    // plus a T_k fan-in segment from each root to FORS pk. This matches FIPS 205
    // §8.4 — verification reconstructs ALL k roots and T_k-aggregates them.
    const forsKeys = [...treeRoots.keys()].filter((k) => k.startsWith('fors:'));
    forsKeys.forEach((key) => {
      const leaf = treeLeaves.get(key);
      const mids = treeMids.get(key) ?? [];
      const root = treeRoots.get(key);
      const path = [leaf, ...mids, root].filter(Boolean);
      for (let j = 0; j + 1 < path.length; j += 1) {
        segments.push([path[j], path[j + 1]]);
      }
      path.forEach((n) => highlights.push(n));
      // T_k fan-in
      if (root && forsPk) segments.push([root, forsPk]);
    });
    if (forsPk) highlights.push(forsPk);

    // Linear chain through d hypertree layers.
    let prev = forsPk;
    for (let i = 0; i < v.d; i += 1) {
      const wots = meshNodes.find((n) => n.kind === 'wots' && n.activeBridge && n.layerIndex === i);
      const key = `xmss:${i}`;
      const leaf = treeLeaves.get(key);
      const mids = treeMids.get(key) ?? [];
      const root = treeRoots.get(key);
      const chain = [prev, wots, leaf, ...mids, root].filter(Boolean);
      for (let j = 0; j + 1 < chain.length; j += 1) {
        segments.push([chain[j], chain[j + 1]]);
      }
      [wots, leaf, ...mids, root].forEach((n) => {
        if (n) highlights.push(n);
      });
      prev = root;
    }

    return { highlights, segments };
  }

  // XMSS subtree drilldown: one leaf, one bridge, the active WOTS+ pk, and an
  // auth path up to the subtree root.
  if (state.view.type === 'xmss') {
    const root = meshNodes.find((node) => node.kind === 'root');
    const activeLeaf = meshNodes.find((node) => node.kind === 'wots-root' && node.activeLeaf);
    const bridge = meshNodes.find((node) => node.kind === 'wots' && node.activeBridge);
    const seq = [];
    if (bridge?.sourceNode) seq.push(bridge.sourceNode);
    if (bridge) seq.push(bridge);
    if (activeLeaf) seq.push(activeLeaf);
    const levelGroups = new Map();
    meshNodes
      .filter((node) => node.kind === 'xmss')
      .forEach((node) => {
        const key = Math.round(node.position.y * 10) / 10;
        if (!levelGroups.has(key)) levelGroups.set(key, []);
        levelGroups.get(key).push(node);
      });
    [...levelGroups.entries()]
      .sort((a, b) => a[0] - b[0])
      .forEach(([level, nodes], i) => {
        const idx = Math.min(nodes.length - 1, Math.floor(hashNoise(state.routeSeed, i + 17) * nodes.length));
        seq.push(nodes[idx]);
      });
    if (root) seq.push(root);
    const ordered = seq.filter(Boolean);
    const segs = [];
    for (let i = 0; i + 1 < ordered.length; i += 1) segs.push([ordered[i], ordered[i + 1]]);
    return { highlights: ordered, segments: segs };
  }

  // FORS forest drilldown: one leaf → one auth node → one tree → root.
  const route = [];
  const grouped = new Map();
  meshNodes.forEach((node) => {
    const key = Math.round(node.position.y * 10) / 10;
    if (!grouped.has(key)) grouped.set(key, []);
    grouped.get(key).push(node);
  });
  [...grouped.entries()]
    .sort((a, b) => a[0] - b[0])
    .forEach(([level, nodes], i) => {
      const idx = Math.min(nodes.length - 1, Math.floor(hashNoise(state.routeSeed, i + state.view.depth) * nodes.length));
      route.push(nodes[idx]);
    });
  const terminalKind = state.view.type === 'fors' ? 'fors' : 'wots';
  const terminal = leafNodes.filter((node) => node.kind === terminalKind);
  if (terminal.length) route.push(terminal[Math.floor(hashNoise(state.routeSeed, 41) * terminal.length) % terminal.length]);
  const ordered = route.filter(Boolean);
  const segs = [];
  for (let i = 0; i + 1 < ordered.length; i += 1) segs.push([ordered[i], ordered[i + 1]]);
  return { highlights: ordered, segments: segs };
}

function refreshRoute() {
  const r = routeNodes();
  currentRoute = r.highlights;
  // Multi-segment route: r.segments is an array of [from, to] pairs; we render
  // them as LineSegments so multiple disconnected paths (one per FORS tree) all
  // light up in yellow without the renderer connecting them across trees.
  const segs = r.segments ?? [];
  const arr = new Float32Array(segs.length * 2 * 3);
  segs.forEach(([a, b], i) => {
    arr.set(a.position.toArray(), i * 6);
    arr.set(b.position.toArray(), i * 6 + 3);
  });
  routeGeometry.setAttribute('position', new BufferAttribute(arr, 3));
  routeGeometry.computeBoundingSphere();
  state.routeCursor = 0;
}

function updateInstances() {
  let count = 0;
  leafNodes.forEach((node) => {
    const onPath = currentRoute.includes(node);
    tmpMatrix.compose(node.position, tmpQuaternion, tmpScale.setScalar(onPath ? 1.85 : 1));
    leafMesh.setMatrixAt(count, tmpMatrix);
    leafMesh.setColorAt(count, onPath ? palette.path : node.color);
    count += 1;
  });
  leafMesh.count = count;
  leafMesh.instanceMatrix.needsUpdate = true;
  if (leafMesh.instanceColor) leafMesh.instanceColor.needsUpdate = true;

  meshNodes.forEach((node) => {
    const onPath = currentRoute.includes(node);
    node.mesh.material.color.copy(onPath ? palette.path : node.color);
    // MeshBasicMaterial has no emissive; brightness on path comes from scale +
    // material.opacity instead.
    node.mesh.material.opacity = onPath ? 1.0 : 0.92;
    node.mesh.scale.setScalar(onPath ? 1.36 : node.baseScale ?? 1);
  });
}

function setNodeCard(node) {
  if (!node) {
    nodeType.textContent = 'Explorer';
    nodeTitle.textContent = state.view.label;
    nodeMeta.textContent = 'Double-click an internal node to zoom inside that subtree.';
    return;
  }
  nodeType.textContent = node.kind.toUpperCase().replace('-', ' ');
  nodeTitle.textContent = node.title;
  nodeMeta.textContent = node.meta;
}

function positionLabel() {
  const v = variant();
  const subtreeHeight = Math.floor(v.h / v.d);
  if (state.view.type === 'hypertree') {
    if (v.d === 1) return `hypertree d=1, h=${v.h}, h/d=${subtreeHeight}`;
    return `hypertree d=${v.d}, h=${v.h}, h/d=${subtreeHeight}`;
  }
  if (state.view.type === 'xmss') return `XMSS d=${state.view.layerIndex ?? 0}, h=${v.h}, h/d=${subtreeHeight}`;
  if (state.view.type === 'wots') return `WOTS+ d=${state.view.layerIndex ?? 0}, l=${v.l}, w=${v.w}`;
  return `FORS forest k=${v.k}, a=${v.a}`;
}

function updateOverview() {
  const v = variant();
  const layerGap = v.d <= 1 ? 0 : 76 / (v.d - 1);
  const xmssRows = [];
  for (let layer = v.d - 1; layer >= 0; layer -= 1) {
    const y = v.d === 1 ? 70 : 34 + (v.d - 1 - layer) * layerGap;
    const isLayer = state.view.layerIndex === layer && (state.view.type === 'xmss' || state.view.type === 'wots');
    xmssRows.push(`
      <line x1="150" y1="${y + 5}" x2="150" y2="${Math.min(132, y + (layerGap || 56) - 10)}" stroke="#f35f8f" stroke-width="${isLayer ? 3 : 1.6}" stroke-opacity="${isLayer ? 0.95 : 0.45}" />
      <rect x="86" y="${y - 11}" width="128" height="22" rx="4" fill="${isLayer && state.view.type === 'xmss' ? 'var(--accent)' : '#10201b'}" stroke="#7cfcbd" stroke-opacity="${isLayer ? 0.95 : 0.45}" />
      <text x="150" y="${y + 4}" text-anchor="middle" fill="${isLayer && state.view.type === 'xmss' ? '#07100d' : '#aab8b2'}">XMSS d=${layer} (h/d=${Math.floor(v.h / v.d)})</text>
    `);
  }
  const forsActive = state.view.type === 'fors';
  overviewMap.innerHTML = `
    <line x1="150" y1="20" x2="150" y2="140" stroke="#43514d" stroke-width="1" stroke-opacity="0.55" />
    <circle cx="150" cy="18" r="8" fill="#f4fff8" opacity="0.95" />
    <text x="166" y="22">pkRoot</text>
    ${xmssRows.join('')}
    <rect x="62" y="126" width="176" height="22" rx="5" fill="${forsActive ? 'var(--accent)' : '#0f2027'}" stroke="#61d6ff" stroke-opacity="${forsActive ? 0.95 : 0.5}" />
    <text x="150" y="141" text-anchor="middle" fill="${forsActive ? '#07100d' : '#aab8b2'}">FORS k=${v.k}, a=${v.a} → digest</text>
  `;
}

function updateParamGrid() {
  const v = variant();
  const cells = [
    ['h', v.h], ['d', v.d], ['a', v.a], ['k', v.k],
    ['w', v.w], ['l', v.l], ['n', v.n],
    ...(v.swn != null ? [['s_wn', v.swn]] : []),
  ];
  paramGrid.innerHTML = cells
    .map(([label, value]) => `<div class="param-cell"><span>${label}</span><strong>${value}</strong></div>`)
    .join('');
}

function updateHud() {
  const v = variant();
  const sec = securityAtBudget(v, state.budgetExponent);
  messageLabel.textContent = messageHex(state.routeSeed);
  messageMeta.textContent = state.view.type === 'hypertree'
    ? `Hmsg → k·a-bit FORS digest + (idx_tree, idx_leaf). Verifier reconstructs k FORS roots → FORS pk → ${v.d} WOTS+/XMSS layers → pkRoot.`
    : 'Same signature route, restricted to the selected component.';
  currentPosition.textContent = positionLabel();
  updateOverview();
  updateParamGrid();
  metricVariant.textContent = v.label;
  metricFamily.textContent = v.family;
  metricSig.textContent = v.sig;
  metricVerify.textContent = v.verify;
  metricSign.textContent = v.signH;
  metricSecurity.textContent = `${sec.toFixed(sec % 1 === 0 ? 0 : 1)}b`;
  budgetValue.textContent = `2^${state.budgetExponent}`;
  document.documentElement.style.setProperty('--accent', v.color);
  backView.disabled = state.stack.length === 0;
  variantButtons.forEach((button) => button.classList.toggle('active', button.dataset.variant === state.variantKey));
  crumbs.innerHTML = '';
  const trail = [{ label: 'Hypertree', current: state.view.type === 'hypertree', stackLength: 0 }];
  state.stack.forEach((item, index) => {
    if (item.type !== 'hypertree') trail.push({ label: item.label, view: item, stackLength: index });
  });
  if (state.view.type !== 'hypertree') {
    trail.push({ label: state.view.label, current: true });
  }
  trail
    .forEach((crumbItem) => {
      const item = document.createElement('button');
      item.className = 'crumb';
      item.textContent = crumbItem.label;
      item.disabled = crumbItem.current;
      item.addEventListener('click', () => jumpToCrumb(crumbItem));
      crumbs.appendChild(item);
    });
  setNodeCard(null);
}

function viewTypeFromNode(node) {
  if (node.kind === 'fors-root' || node.kind === 'fors' || node.kind === 'fors-pk') return 'fors';
  if (node.kind.startsWith('wots')) return 'wots';
  // XMSS leaves ARE WOTS+ pks → drill into the WOTS chain view.
  if (node.id?.startsWith('tree-leaf-') && node.kind === 'xmss') return 'wots';
  return 'xmss';
}

function zoomInto(node) {
  if (!node?.zoomable || inceptionTween) return;
  const focus = node.mesh.position.clone();
  const newView = {
    type: viewTypeFromNode(node),
    label: node.title,
    depth: state.stack.length + 1,
    seed: node.seed,
    layerIndex: node.layerIndex,
    node,
  };
  startInception('in', focus, () => {
    state.stack.push({ ...state.view });
    state.view = newView;
    rebuild();
    focusScene(false);
  });
}

function goBack() {
  if (!state.stack.length || inceptionTween) return;
  // Inception "out": scene shrinks toward the origin (where the parent node would have been).
  const focus = currentRoot?.mesh?.position?.clone() ?? new Vector3(0, 0, 0);
  startInception('out', focus, () => {
    state.view = state.stack.pop();
    rebuild();
    focusScene(false);
  });
}

function resetExplorer() {
  state.stack.length = 0;
  state.view = { type: 'hypertree', label: 'Hypertree', depth: 0, seed: state.routeSeed };
  rebuild();
  // Centre camera on the variant's scene midpoint, axis-aligned (no tilt).
  const my = sceneMidY();
  camera.position.set(0, my, 28);
  controls.target.set(0, my, 0);
}

function selectVariant(key) {
  state.variantKey = key;
  state.stack.length = 0;
  state.view = { type: 'hypertree', label: 'Hypertree', depth: 0, seed: state.routeSeed };
  // Trees are entirely different per variant — discard per-tree user expansion.
  expandedLevelsByTree.clear();
  rebuild();
}

function jumpToCrumb(crumbItem) {
  if (crumbItem.stackLength === 0) {
    state.stack.length = 0;
    state.view = { type: 'hypertree', label: 'Hypertree', depth: 0, seed: state.routeSeed };
  } else {
    const target = crumbItem.view;
    state.stack.length = crumbItem.stackLength;
    state.view = { ...target };
  }
  rebuild();
  focusScene(true);
}

// 2D-mode framing: camera always looks straight down -z, centred on the scene
// midpoint, biased slightly toward the bottom so the FORS sig bar + formula
// label always clear the bottom HUD overlays.
function sceneMidY() {
  const v = variant();
  const layerHeight = Math.min(2.2, 10 / Math.max(2, v.d));
  const pkRootY = -0.3 + 1.0 + v.d * layerHeight;
  const bottomY = -7.0;
  // Biased so the bottom region (formula) stays visible even for tall (d=5)
  // variants. Pure midpoint would push the formula below the HUD on C12.
  return bottomY * 0.55 + pkRootY * 0.45 - 0.2;
}

function focusScene(animated = true) {
  let target;
  let pos;
  if (state.view.type === 'hypertree') {
    const my = sceneMidY();
    target = new Vector3(0, my, 0);
    pos = new Vector3(0, my, 28);
  } else {
    const t = currentRoot?.position ?? new Vector3(0, 0, 0);
    target = t.clone();
    pos = new Vector3(t.x, t.y, 18);
  }
  if (!animated) {
    controls.target.copy(target);
    camera.position.copy(pos);
    return;
  }
  cameraTween = {
    fromPosition: camera.position.clone(),
    toPosition: pos,
    fromTarget: controls.target.clone(),
    toTarget: target.clone(),
    startedAt: performance.now(),
    duration: 620,
  };
}

const raycaster = new Raycaster();
// Tighter line threshold so nearby node hits beat edge hits — important when
// hovering a leaf, where the connecting edge starts inside the leaf mesh.
raycaster.params.Line.threshold = 0.04;
const pointer = new Vector2(-10, -10);

function pickNode(event) {
  pointer.x = (event.clientX / window.innerWidth) * 2 - 1;
  pointer.y = -(event.clientY / window.innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObjects(selectable, true);
  if (!hits[0]) {
    state.hoverId = null;
    canvas.style.cursor = 'default';
    return;
  }
  // Walk the hits in order; meshes win over lines, but dashed truncation
  // edges are interactive too.
  for (const hit of hits) {
    const obj = hit.object;
    // Sig-bar cell (sk box / auth body) — has its own meta.
    if (obj.userData.cellInfo) {
      const info = obj.userData.cellInfo;
      canvas.style.cursor = 'default';
      state.hoverId = `cell-${obj.id}`;
      setNodeCard({ kind: info.kind, title: info.title, meta: info.meta });
      return;
    }
    // Direct mesh node
    if (obj.userData.node) {
      const node = obj.userData.node;
      canvas.style.cursor = 'default';
      state.hoverId = node.id;
      setNodeCard(node);
      return;
    }
    // Per-instance ghost in InstancedMesh
    if (obj.userData.ghostInfo && hit.instanceId !== undefined) {
      const info = obj.userData.ghostInfo[hit.instanceId];
      if (info) {
        canvas.style.cursor = 'default';
        state.hoverId = `ghost-${obj.id}-${hit.instanceId}`;
        setNodeCard({ kind: info.kind, title: info.title, meta: info.meta });
        return;
      }
    }
    // Dashed truncation edge — clickable to expand.
    if (obj.userData.dashedMeta && hit.index !== undefined) {
      const segIdx = Math.floor(hit.index / 2);
      const info = obj.userData.dashedMeta[segIdx];
      if (info) {
        canvas.style.cursor = 'pointer';
        state.hoverId = `dashed-${obj.id}-${segIdx}`;
        setNodeCard({
          kind: 'truncation',
          title: `Truncation in ${info.kind === 'fors-root' ? 'FORS' : 'XMSS'} tree`,
          meta: `This single dashed edge represents ${info.truncated} compressed Merkle levels (real depth ${info.realDepth}, drawn depth ${info.visibleDepth}). Click to reveal one more level.`,
        });
        return;
      }
    }
    // Plain edge — show what cryptographic operation it represents.
    if (obj.userData.edgeMeta && hit.index !== undefined) {
      const segIdx = Math.floor(hit.index / 2);
      const info = obj.userData.edgeMeta[segIdx];
      if (info) {
        canvas.style.cursor = 'default';
        state.hoverId = `edge-${obj.id}-${segIdx}`;
        setNodeCard({ kind: info.kind, title: info.title, meta: info.meta });
        return;
      }
    }
  }
  canvas.style.cursor = 'default';
  state.hoverId = null;
}

function nodeFromPointer(event) {
  pointer.x = (event.clientX / window.innerWidth) * 2 - 1;
  pointer.y = -(event.clientY / window.innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  return raycaster.intersectObjects(selectable, false)[0]?.object.userData.node ?? null;
}

function nearestZoomableNode(event) {
  const projected = new Vector3();
  let nearest = null;
  let nearestDistance = Infinity;
  selectable.forEach((mesh) => {
    const node = mesh.userData.node;
    if (!node?.zoomable) return;
    projected.copy(mesh.position).project(camera);
    const x = (projected.x * 0.5 + 0.5) * window.innerWidth;
    const y = (-projected.y * 0.5 + 0.5) * window.innerHeight;
    const distance = Math.hypot(x - event.clientX, y - event.clientY);
    if (distance < nearestDistance) {
      nearestDistance = distance;
      nearest = node;
    }
  });
  return nearest;
}

canvas.addEventListener('pointermove', pickNode);
function dashedHitFromPointer(event) {
  pointer.x = (event.clientX / window.innerWidth) * 2 - 1;
  pointer.y = -(event.clientY / window.innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObjects(selectable, true);
  for (const hit of hits) {
    const obj = hit.object;
    if (obj.userData?.dashedMeta && hit.index !== undefined) {
      const info = obj.userData.dashedMeta[Math.floor(hit.index / 2)];
      if (info?.treeKey) return info.treeKey;
    }
  }
  return null;
}

canvas.addEventListener('click', (event) => {
  const node = nodeFromPointer(event);
  if (!node) return;
  // Triangle nodes (WOTS+ family) drill straight into the WOTS chain view on
  // a single click — they're the WOTS+ verifier, that's where they go.
  if (nodeFamily(node) === 'wots' && node.zoomable && state.view.type !== 'wots') {
    zoomInto(node);
    return;
  }
  controls.target.copy(node.position);
  setNodeCard(node);
});
canvas.addEventListener('dblclick', (event) => {
  // Double-click on a dashed truncation edge → reveal one more compressed
  // level of that tree (and re-render with thinner nodes for revealed levels).
  const treeKey = dashedHitFromPointer(event);
  if (treeKey) {
    expandedLevelsByTree.set(treeKey, (expandedLevelsByTree.get(treeKey) ?? 0) + 1);
    rebuild();
    return;
  }
  const node = nodeFromPointer(event) ?? nearestZoomableNode(event);
  zoomInto(node);
});

backView.addEventListener('click', goBack);
variantButtons.forEach((button) => {
  button.addEventListener('click', () => selectVariant(button.dataset.variant));
});
budgetRange.addEventListener('input', () => {
  state.budgetExponent = Number(budgetRange.value);
  updateHud();
});
rerouteButton.addEventListener('click', () => {
  state.routeSeed += 1;
  refreshRoute();
  updateInstances();
  updateHud();
});
resetViewButton.addEventListener('click', resetExplorer);
playToggle.addEventListener('click', () => {
  state.playing = !state.playing;
  playToggle.classList.toggle('active', state.playing);
  playToggle.title = state.playing ? 'Pause animation' : 'Play animation';
  playToggle.innerHTML = state.playing ? '<i data-lucide="pause"></i>' : '<i data-lucide="play"></i>';
  createIcons({ icons: { Pause, Play } });
});

function resize() {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
  // LineMaterial needs the viewport resolution to scale line width correctly.
  ghostMeshes.forEach((m) => {
    if (m.userData?.lineMaterial) {
      m.userData.lineMaterial.resolution.set(window.innerWidth, window.innerHeight);
    }
  });
}
window.addEventListener('resize', resize);

function easeInOutCubic(t) {
  return t < 0.5 ? 4 * t * t * t : 1 - ((-2 * t + 2) ** 3) / 2;
}

const clock = new Clock();
function animate() {
  const elapsed = clock.getElapsedTime();
  const delta = clock.getDelta();
  if (cameraTween) {
    const raw = Math.min(1, (performance.now() - cameraTween.startedAt) / cameraTween.duration);
    const eased = 1 - (1 - raw) ** 3;
    camera.position.copy(cameraTween.fromPosition).lerp(cameraTween.toPosition, eased);
    controls.target.copy(cameraTween.fromTarget).lerp(cameraTween.toTarget, eased);
    if (raw >= 1) cameraTween = null;
  }
  if (inceptionTween) {
    const raw = Math.min(1, (performance.now() - inceptionTween.startedAt) / inceptionTween.duration);
    const eased = easeInOutCubic(raw);
    if (inceptionTween.phase === 'depart') {
      // Pull *into* the focus node (zoom in) or *away from* it (zoom out).
      const direction = inceptionTween.direction === 'in' ? 1 : -1;
      const scale = inceptionTween.direction === 'in' ? 1 + eased * 5.5 : 1 - eased * 0.6;
      world.scale.setScalar(Math.max(0.001, scale));
      const f = inceptionTween.focus;
      world.position.set(-f.x * (scale - 1), -f.y * (scale - 1), -f.z * (scale - 1));
      inceptionOverlay.style.opacity = String(eased);
      // Camera lurches in the same direction as the world expansion.
      const lurch = direction * eased * 1.2;
      camera.position.z -= lurch * delta * 60;
      if (raw >= 1) {
        if (typeof inceptionTween.onMid === 'function') inceptionTween.onMid();
        inceptionTween = {
          direction: inceptionTween.direction,
          focus: new Vector3(),
          startedAt: performance.now(),
          duration: 460,
          phase: 'arrive',
        };
        // start "arrive" with world prescaled to opposite extreme so it animates into normal.
        if (inceptionTween.direction === 'in') {
          world.scale.setScalar(0.45);
        } else {
          world.scale.setScalar(2.4);
        }
        world.position.set(0, 0, 0);
      }
    } else if (inceptionTween.phase === 'arrive') {
      const startScale = inceptionTween.direction === 'in' ? 0.45 : 2.4;
      const scale = startScale + (1 - startScale) * eased;
      world.scale.setScalar(scale);
      inceptionOverlay.style.opacity = String(1 - eased);
      if (raw >= 1) {
        world.scale.setScalar(1);
        world.position.set(0, 0, 0);
        inceptionOverlay.style.opacity = '0';
        inceptionTween = null;
      }
    }
  }
  if (state.playing) {
    // 2D view: no auto-rotation. Keep the route-pulse cursor advancing.
    state.routeCursor = (state.routeCursor + delta * 0.24) % 1;
  }
  meshNodes.forEach((node, index) => {
    const onPath = currentRoute.includes(node);
    const hover = node.id === state.hoverId;
    // 2D: no per-node bobbing or rotation — pure scale-pulse for the active path.
    node.mesh.position.y = node.position.y;
    node.mesh.scale.setScalar(onPath ? 1.28 + Math.sin(elapsed * 3.2) * 0.06 : hover ? 1.2 : node.baseScale ?? 1);
  });
  if (routeGeometry?.attributes.position?.count) {
    const points = routeGeometry.attributes.position;
    pulse.position.fromBufferAttribute(points, Math.floor(state.routeCursor * (points.count - 1)));
    pulse.scale.setScalar(1 + Math.sin(elapsed * 8) * 0.18);
  }
  if (currentRoot?.mesh) {
    rootRing.position.copy(currentRoot.mesh.position);
    rootRing.rotation.x = elapsed * 0.5;
    rootRing.rotation.y = elapsed * 0.32;
  }
  leafMesh.rotation.y = Math.sin(elapsed * 0.5) * 0.014;
  controls.update();
  // Labels need world.matrixWorld up to date — controls.update updates camera; force world matrix.
  world.updateMatrixWorld();
  if (inceptionTween) {
    labelLayer.style.opacity = String(Math.max(0, 1 - Number(inceptionOverlay.style.opacity || 0) * 1.6));
  } else {
    labelLayer.style.opacity = '1';
  }
  updateNodeLabels();
  renderer.render(scene, camera);
  requestAnimationFrame(animate);
}

rebuild();
resize();
animate();

// Vite HMR: dispose the WebGL context, all DOM overlays, the world group's
// children, and event listeners before the module is replaced. Without this,
// each hot reload allocates a new WebGLRenderer + canvas while leaving the
// old one alive, eventually exhausting the browser's WebGL-context budget
// (Chrome blocks at ~16 contexts → "Web page caused context loss" error).
if (import.meta.hot) {
  import.meta.hot.dispose(() => {
    try { clearModel(); } catch (_) {}
    try { renderer.dispose(); } catch (_) {}
    try { renderer.forceContextLoss?.(); } catch (_) {}
    try { renderer.domElement?.remove(); } catch (_) {}
    try { inceptionOverlay.remove(); } catch (_) {}
    try { labelLayer.remove(); } catch (_) {}
    window.removeEventListener('resize', resize);
  });
}
