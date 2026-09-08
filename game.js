(() => {
  'use strict';

  const canvas = document.getElementById('gameCanvas');
  const ctx = canvas.getContext('2d');
  const qrInput = document.getElementById('qrInput');
  const generateBtn = document.getElementById('generateBtn');
  const scanBtn = document.getElementById('scanBtn');
  const foodScoreEl = document.getElementById('foodScore');
  const workerCountEl = document.getElementById('workerCount');
  const populationCountEl = document.getElementById('populationCount');
  const populationBarEl = document.getElementById('populationBar');
  const buffTextEl = document.getElementById('buffText');
  const discoveredCountEl = document.getElementById('discoveredCount');
  const missionTextEl = document.getElementById('missionText');
  const gameStateBadge = document.getElementById('gameStateBadge');
  const toastEl = document.getElementById('toast');
  const chapterNumberEl = document.getElementById('chapterNumber');
  const chapterTitleEl = document.getElementById('chapterTitle');
  const chapterDescEl = document.getElementById('chapterDesc');
  const statLabel1El = document.getElementById('statLabel1');
  const statLabel2El = document.getElementById('statLabel2');
  const statLabel3El = document.getElementById('statLabel3');
  const statLabel4El = document.getElementById('statLabel4');
  const nextLevelBtn = document.getElementById('nextLevelBtn');
  const legendCardEl = document.getElementById('legendCard');
  const roadmap1El = document.getElementById('roadmap1');
  const roadmap2El = document.getElementById('roadmap2');
  const roadmap3El = document.getElementById('roadmap3');
  const roadmap4El = document.getElementById('roadmap4');

  const POPULATION_TARGET = 10;
  const START_POPULATION = 3;
  const FOOD_PER_BIRTH = 2;
  const QUIET = 4;
  const MOVE_COOLDOWN = 55;
  const BOOSTED_MOVE_COOLDOWN = 45;
  const LEVEL2_SECONDS = 90;
  const LEVEL2_ENTRANCE_COUNT = 2;
  const MUD_REQUIRED_PER_ENTRANCE = 3;
  const LEVEL2_WORKER_LIMIT = 4;

  let qr = null;
  let matrixSize = 0;
  let graph = null;
  let component = [];
  let componentSet = new Set();
  let nest = null;
  let player = null;
  let foods = [];
  let workers = [];
  let pheromoneRoutes = [];
  let discovered = 0;
  let storedFood = 0;
  let population = START_POPULATION;
  let bonusPopulation = 0;
  let workerLimit = START_POPULATION - 1;
  let scanMode = false;
  let status = 'playing';
  let lastMoveTime = 0;
  let toastTimer = null;
  let carriedDiscovery = null;
  let returnTrail = [];
  let speedBoostUntil = 0;
  let activeBuffLabel = '';
  let renderRequest = null;

  let currentLevel = 1;
  let level2Unlocked = false;
  let mudSources = [];
  let entrances = [];
  let carryingMud = false;
  let carriedMudSource = null;
  let mudTrail = [];
  let mudWorkers = [];
  let level2StartTime = 0;
  let level2RainStarted = false;
  let flooded = new Set();
  let floodFrontier = [];
  let lastFloodTick = 0;
  let scanPauseStarted = 0;

  function nodeKey(r, c) { return `${r},${c}`; }
  function parseKey(key) { const [r, c] = key.split(',').map(Number); return { r, c }; }
  function sameNode(a, b) { return a && b && a.r === b.r && a.c === b.c; }

  function isDark(r, c) {
    return r >= 0 && c >= 0 && r < matrixSize && c < matrixSize && qr.isDark(r, c);
  }

  // Nodes sit on QR module corners. An edge is blocked only when it runs between
  // two dark modules. This turns contiguous dark QR regions into solid soil walls
  // while leaving a connected tunnel network around them without changing the QR.
  function buildGraph() {
    const size = matrixSize + 1;
    const neighbors = new Map();

    for (let r = 0; r < size; r++) {
      for (let c = 0; c < size; c++) {
        const list = [];

        if (c + 1 < size) {
          const aboveDark = isDark(r - 1, c);
          const belowDark = isDark(r, c);
          if (!(aboveDark && belowDark)) list.push({ r, c: c + 1 });
        }
        if (c - 1 >= 0) {
          const aboveDark = isDark(r - 1, c - 1);
          const belowDark = isDark(r, c - 1);
          if (!(aboveDark && belowDark)) list.push({ r, c: c - 1 });
        }
        if (r + 1 < size) {
          const leftDark = isDark(r, c - 1);
          const rightDark = isDark(r, c);
          if (!(leftDark && rightDark)) list.push({ r: r + 1, c });
        }
        if (r - 1 >= 0) {
          const leftDark = isDark(r - 1, c - 1);
          const rightDark = isDark(r - 1, c);
          if (!(leftDark && rightDark)) list.push({ r: r - 1, c });
        }

        if (r === 0 || c === 0 || r === size - 1 || c === size - 1) {
          neighbors.set(nodeKey(r, c), []);
        } else {
          neighbors.set(
            nodeKey(r, c),
            list.filter(n => n.r > 0 && n.c > 0 && n.r < size - 1 && n.c < size - 1)
          );
        }
      }
    }
    return neighbors;
  }

  function largestComponent() {
    const seen = new Set();
    let best = [];
    for (const key of graph.keys()) {
      if (seen.has(key) || graph.get(key).length === 0) continue;
      const queue = [key];
      const group = [];
      seen.add(key);
      while (queue.length) {
        const k = queue.shift();
        group.push(parseKey(k));
        for (const n of graph.get(k)) {
          const nk = nodeKey(n.r, n.c);
          if (!seen.has(nk)) {
            seen.add(nk);
            queue.push(nk);
          }
        }
      }
      if (group.length > best.length) best = group;
    }
    return best;
  }

  function bfsPath(start, goal) {
    if (!start || !goal) return null;
    const startK = nodeKey(start.r, start.c);
    const goalK = nodeKey(goal.r, goal.c);
    if (startK === goalK) return [{ ...start }];
    const q = [startK];
    const prev = new Map([[startK, null]]);
    while (q.length) {
      const k = q.shift();
      for (const n of graph.get(k) || []) {
        const nk = nodeKey(n.r, n.c);
        if (!componentSet.has(nk) || prev.has(nk)) continue;
        prev.set(nk, k);
        if (nk === goalK) {
          const path = [];
          let cur = nk;
          while (cur !== null) {
            path.push(parseKey(cur));
            cur = prev.get(cur);
          }
          return path.reverse();
        }
        q.push(nk);
      }
    }
    return null;
  }

  function distanceMap(start) {
    const dist = new Map();
    const sk = nodeKey(start.r, start.c);
    const q = [sk];
    dist.set(sk, 0);
    while (q.length) {
      const k = q.shift();
      const d = dist.get(k);
      for (const n of graph.get(k) || []) {
        const nk = nodeKey(n.r, n.c);
        if (!componentSet.has(nk) || dist.has(nk)) continue;
        dist.set(nk, d + 1);
        q.push(nk);
      }
    }
    return dist;
  }

  function pickNest() {
    const center = matrixSize / 2;
    const candidates = component.filter(
      n => n.r > 4 && n.c > 4 && n.r < matrixSize - 4 && n.c < matrixSize - 4
    );
    const pool = candidates.length ? candidates : component;
    return pool.reduce((best, n) => {
      const d = Math.hypot(n.r - center, n.c - center);
      return !best || d < best.d ? { node: n, d } : best;
    }, null).node;
  }

  function pickFoodNodes(count) {
    const dist = distanceMap(nest);
    const minDistance = Math.max(6, Math.floor(matrixSize * .18));
    const maxDistance = Math.max(minDistance + 4, Math.floor(matrixSize * 1.25));

    const isFinderZone = node => {
      const pad = 9;
      const inTop = node.r <= pad;
      const inLeft = node.c <= pad;
      const inRight = node.c >= matrixSize - pad;
      const inBottom = node.r >= matrixSize - pad;
      return (inTop && inLeft) || (inTop && inRight) || (inBottom && inLeft);
    };

    // Every candidate comes from the largest connected component, so it is
    // reachable from the nest. We additionally require a nearby white module
    // for the visible food icon, and avoid the three QR finder patterns.
    const candidates = component
      .filter(n => {
        const d = dist.get(nodeKey(n.r, n.c));
        return (
          Number.isFinite(d) &&
          d >= minDistance &&
          d <= maxDistance &&
          !sameNode(n, nest) &&
          !isFinderZone(n) &&
          !!chooseFoodDisplayCell(n)
        );
      });

    // Fisher-Yates shuffle: the same QR gets different food positions each run.
    for (let i = candidates.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [candidates[i], candidates[j]] = [candidates[j], candidates[i]];
    }

    const chosen = [];
    const usedCells = new Set();
    const preferredSpacing = Math.max(3, matrixSize * .11);

    for (const n of candidates) {
      const cell = chooseFoodDisplayCell(n);
      if (!cell) continue;
      const cellKey = nodeKey(cell.r, cell.c);
      if (usedCells.has(cellKey)) continue;

      const farEnough = chosen.every(
        other => Math.hypot(other.r - n.r, other.c - n.c) >= preferredSpacing
      );
      if (!farEnough) continue;

      chosen.push({ ...n });
      usedCells.add(cellKey);
      if (chosen.length >= count) break;
    }

    // Fallback only relaxes spacing; reachability and a valid white display
    // cell remain mandatory.
    if (chosen.length < count) {
      for (const n of candidates) {
        if (chosen.length >= count) break;
        if (chosen.some(other => sameNode(other, n))) continue;
        const cell = chooseFoodDisplayCell(n);
        if (!cell) continue;
        const cellKey = nodeKey(cell.r, cell.c);
        if (usedCells.has(cellKey)) continue;
        chosen.push({ ...n });
        usedCells.add(cellKey);
      }
    }

    return chosen;
  }

  // Food is logically attached to a reachable graph node, but visually placed
  // in the centre of a nearby WHITE QR module. This keeps it readable instead
  // of letting a tiny icon sit on top of a black QR block.
  function chooseFoodDisplayCell(node) {
    const cells = [
      { r: node.r - 1, c: node.c - 1 },
      { r: node.r - 1, c: node.c },
      { r: node.r, c: node.c - 1 },
      { r: node.r, c: node.c }
    ].filter(cell =>
      cell.r >= 0 && cell.c >= 0 &&
      cell.r < matrixSize && cell.c < matrixSize &&
      !isDark(cell.r, cell.c)
    );

    if (!cells.length) return null;

    // Prefer a white cell that sits among more white neighbours, so the food
    // looks like it is lying in an actual passage rather than on a thin seam.
    cells.sort((a, b) => {
      const score = cell => {
        let s = 0;
        [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr, dc]) => {
          const rr = cell.r + dr, cc = cell.c + dc;
          if (rr >= 0 && cc >= 0 && rr < matrixSize && cc < matrixSize && !isDark(rr, cc)) s += 1;
        });
        return s;
      };
      return score(b) - score(a);
    });
    return cells[0];
  }

  function foodScreenPosition(food) {
    if (!food.displayCell) return nodeXY(food);
    const { step, offset } = boardMetrics();
    return {
      x: offset + (food.displayCell.c + .5) * step,
      y: offset + (food.displayCell.r + .5) * step
    };
  }

  function playerTouchesFood(food) {
    if (!food.displayCell) return sameNode(food, player);
    const r = food.displayCell.r;
    const c = food.displayCell.c;
    return (
      (player.r === r && player.c === c) ||
      (player.r === r && player.c === c + 1) ||
      (player.r === r + 1 && player.c === c) ||
      (player.r === r + 1 && player.c === c + 1)
    );
  }


  function setRoadmapActive(level) {
    [roadmap1El, roadmap2El, roadmap3El, roadmap4El].forEach((el, i) => {
      if (!el) return;
      const n = i + 1;
      el.classList.toggle('active', n === level);
      if (n === 1) {
        el.classList.remove('locked');
        el.classList.add('unlocked');
      } else if (n === 2 && level2Unlocked) {
        el.classList.remove('locked');
        el.classList.add('unlocked');
      } else {
        el.classList.add('locked');
        el.classList.remove('unlocked');
      }
    });
  }

  function setLevelOneUI() {
    chapterNumberEl.textContent = '第 1 关';
    chapterTitleEl.textContent = '第一顿饭';
    chapterDescEl.textContent = '不限时间。找到食物并带回气味，让工蚁开始运输，把蚁群人口养到 10。';
    statLabel1El.textContent = '蚁群人口';
    statLabel2El.textContent = '储备食物';
    statLabel3El.textContent = '运输工蚁';
    statLabel4El.textContent = '发现食物';
    legendCardEl.innerHTML = `
      <h2>一眼看懂</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：黄色蚂蚁</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>工蚁：橙色蚂蚁</span></div>
      <div class="legend"><span>🍩</span><span>Lv.1 甜甜圈 · 2份</span></div>
      <div class="legend"><span>🧁</span><span>Lv.2 杯子蛋糕 · 3份 · 加速15秒</span></div>
      <div class="legend"><span>🍰</span><span>Lv.3 草莓蛋糕 · 5份 · 额外孵化+1</span></div>
      <div class="legend"><span class="legend-nest"></span><span>蚁穴：绿色圆环</span></div>
    `;
    nextLevelBtn.hidden = true;
    setRoadmapActive(1);
  }

  function setLevelTwoUI() {
    chapterNumberEl.textContent = '第 2 关';
    chapterTitleEl.textContent = '暴雨来了';
    chapterDescEl.textContent = '90秒内找到泥土，把第一块泥送到每个入口。工蚁会沿你走过的施工路线继续搬运。';
    statLabel1El.textContent = '封堵入口';
    statLabel2El.textContent = '携带泥土';
    statLabel3El.textContent = '施工工蚁';
    statLabel4El.textContent = '暴雨倒计时';
    legendCardEl.innerHTML = `
      <h2>一眼看懂</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：黄色蚂蚁</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>施工工蚁：橙色蚂蚁</span></div>
      <div class="legend"><span style="font-size:16px">🟤</span><span>泥土：碰到后自动扛起</span></div>
      <div class="legend"><span style="color:#5dc8ff;font-size:18px">◎</span><span>入口：每个需要3块泥</span></div>
      <div class="legend"><span class="legend-water"></span><span>积水：暴雨后沿通道涌入</span></div>
      <div class="legend"><span class="legend-nest"></span><span>蚁穴：不能被水淹到</span></div>
    `;
    nextLevelBtn.hidden = true;
    setRoadmapActive(2);
  }

  function isFinderZoneNode(node) {
    const pad = 9;
    const inTop = node.r <= pad;
    const inLeft = node.c <= pad;
    const inRight = node.c >= matrixSize - pad;
    const inBottom = node.r >= matrixSize - pad;
    return (inTop && inLeft) || (inTop && inRight) || (inBottom && inLeft);
  }

  function shuffled(items) {
    const arr = items.slice();
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  function pickLevelTwoEntrances(count) {
    const dist = distanceMap(nest);
    const candidates = shuffled(component.filter(n => {
      const nearEdge = n.r <= 2 || n.c <= 2 || n.r >= matrixSize - 2 || n.c >= matrixSize - 2;
      const d = dist.get(nodeKey(n.r, n.c));
      return nearEdge && Number.isFinite(d) && d >= Math.max(10, matrixSize * .22) && !isFinderZoneNode(n);
    }));

    const chosen = [];
    for (const n of candidates) {
      if (chosen.every(e => Math.hypot(e.r - n.r, e.c - n.c) >= matrixSize * .35)) {
        chosen.push({
          ...n,
          id: `entrance-${chosen.length}-${Date.now()}`,
          progress: 0,
          required: MUD_REQUIRED_PER_ENTRANCE,
          sealed: false,
          route: null,
          sourceId: null
        });
        if (chosen.length >= count) break;
      }
    }

    for (const n of candidates) {
      if (chosen.length >= count) break;
      if (chosen.some(e => sameNode(e, n))) continue;
      chosen.push({
        ...n,
        id: `entrance-${chosen.length}-${Date.now()}`,
        progress: 0,
        required: MUD_REQUIRED_PER_ENTRANCE,
        sealed: false,
        route: null,
        sourceId: null
      });
    }
    return chosen;
  }

  function pickMudSources(count) {
    const dist = distanceMap(nest);
    const candidates = shuffled(component.filter(n => {
      const d = dist.get(nodeKey(n.r, n.c));
      return (
        Number.isFinite(d) &&
        d >= Math.max(5, matrixSize * .12) &&
        d <= Math.max(18, matrixSize * .72) &&
        !isFinderZoneNode(n) &&
        !!chooseFoodDisplayCell(n) &&
        entrances.every(e => Math.hypot(e.r - n.r, e.c - n.c) >= matrixSize * .14)
      );
    }));

    const chosen = [];
    const usedCells = new Set();
    for (const n of candidates) {
      const cell = chooseFoodDisplayCell(n);
      if (!cell) continue;
      const ck = nodeKey(cell.r, cell.c);
      if (usedCells.has(ck)) continue;
      if (chosen.every(s => Math.hypot(s.r - n.r, s.c - n.c) >= matrixSize * .18)) {
        chosen.push({
          ...n,
          id: `mud-${chosen.length}-${Date.now()}`,
          displayCell: cell
        });
        usedCells.add(ck);
        if (chosen.length >= count) break;
      }
    }
    return chosen;
  }

  function resetGame(content) {
    if (typeof qrcode !== 'function') {
      showToast('二维码库加载失败，请检查网络后刷新。', 3200);
      return;
    }

    qr = qrcode(0, 'H');
    qr.addData(content || 'QR Ant Colony');
    qr.make();
    matrixSize = qr.getModuleCount();
    graph = buildGraph();
    component = largestComponent();
    componentSet = new Set(component.map(n => nodeKey(n.r, n.c)));

    if (!component.length) {
      showToast('这个二维码没有生成可玩的通道，请换一段内容。', 3200);
      return;
    }

    nest = { ...pickNest() };
    player = { ...nest, facing: 'right' };
    const foodNodes = pickFoodNodes(5);
    const foodTiers = [
      { kind: 'donut', units: 2, level: 1, name: '甜甜圈' },
      { kind: 'cupcake', units: 3, level: 2, name: '杯子蛋糕' },
      { kind: 'cake', units: 5, level: 3, name: '草莓蛋糕' },
      { kind: 'donut', units: 2, level: 1, name: '甜甜圈' },
      { kind: 'cupcake', units: 3, level: 2, name: '杯子蛋糕' }
    ];
    for (let i = foodTiers.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [foodTiers[i], foodTiers[j]] = [foodTiers[j], foodTiers[i]];
    }
    foods = foodNodes.map((node, i) => {
      const tier = foodTiers[i % foodTiers.length];
      return {
        ...node,
        id: `food-${Date.now()}-${i}`,
        units: tier.units,
        maxUnits: tier.units,
        kind: tier.kind,
        level: tier.level,
        foodName: tier.name,
        displayCell: chooseFoodDisplayCell(node),
        discovered: false,
        routeActivated: false
      };
    });

    currentLevel = 1;
    workers = [];
    pheromoneRoutes = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    carryingMud = false;
    carriedMudSource = null;
    mudTrail = [];
    flooded = new Set();
    floodFrontier = [];
    level2RainStarted = false;
    level2StartTime = 0;
    lastFloodTick = 0;
    discovered = 0;
    storedFood = 0;
    population = START_POPULATION;
    bonusPopulation = 0;
    workerLimit = START_POPULATION - 1;
    scanMode = false;
    status = 'playing';
    lastMoveTime = 0;
    carriedDiscovery = null;
    returnTrail = [];
    speedBoostUntil = 0;
    activeBuffLabel = '';
    scanBtn.textContent = '扫码模式';
    setLevelOneUI();
    gameStateBadge.textContent = '第1关 · 教学';
    gameStateBadge.style.color = '';
    missionTextEl.textContent = '先熟悉移动，去白色通道里找到第一份食物。';
    updateUI();
    showToast('第1关：第一顿饭。不限时间，把人口养到10只！', 2800);
    requestRender();
  }

  function updateUI(now = performance.now()) {
    if (currentLevel === 2) {
      const sealed = entrances.filter(e => e.sealed).length;
      populationCountEl.textContent = `${sealed} / ${entrances.length || LEVEL2_ENTRANCE_COUNT}`;
      foodScoreEl.textContent = carryingMud ? '1块' : '0块';
      workerCountEl.textContent = String(mudWorkers.length);
      const left = Math.max(0, Math.ceil(LEVEL2_SECONDS - (now - level2StartTime) / 1000));
      discoveredCountEl.textContent = level2RainStarted ? '进水中' : `${left}s`;
      populationBarEl.style.width = `${entrances.length ? (sealed / entrances.length) * 100 : 0}%`;
      buffTextEl.textContent = carryingMud
        ? '🟤 正在搬泥：把它送到蓝色入口'
        : '施工诀窍：你先送1块，工蚁就会沿你的路线接力';
      return;
    }

    foodScoreEl.textContent = String(storedFood);
    workerCountEl.textContent = String(workerLimit);
    populationCountEl.textContent = `${population} / ${POPULATION_TARGET}`;
    populationBarEl.style.width = `${Math.min(100, (population / POPULATION_TARGET) * 100)}%`;
    discoveredCountEl.textContent = String(discovered);

    if (now < speedBoostUntil) {
      const seconds = Math.max(1, Math.ceil((speedBoostUntil - now) / 1000));
      buffTextEl.textContent = `🧁 糖分冲刺：移动更快 · ${seconds}s`;
    } else if (activeBuffLabel) {
      buffTextEl.textContent = activeBuffLabel;
      activeBuffLabel = '';
    } else {
      buffTextEl.textContent = '暂无 · 🧁可加速，🍰可额外孵化';
    }
  }

  function currentMoveCooldown() {
    return performance.now() < speedBoostUntil ? BOOSTED_MOVE_COOLDOWN : MOVE_COOLDOWN;
  }

  function showToast(message, duration = 1900) {
    toastEl.textContent = message;
    toastEl.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toastEl.classList.remove('show'), duration);
  }

  function getMoveTarget(dir) {
    const delta = {
      up: [-1, 0],
      down: [1, 0],
      left: [0, -1],
      right: [0, 1]
    }[dir];
    if (!delta) return null;
    const target = { r: player.r + delta[0], c: player.c + delta[1] };
    const allowed = (graph.get(nodeKey(player.r, player.c)) || []).some(n => sameNode(n, target));
    return allowed && componentSet.has(nodeKey(target.r, target.c)) ? target : null;
  }

  function movePlayer(dir) {
    if (scanMode || status !== 'playing') return;
    const now = performance.now();
    if (now - lastMoveTime < currentMoveCooldown()) return;
    const target = getMoveTarget(dir);
    player.facing = dir;
    lastMoveTime = now;

    if (!target) {
      showToast('这边是实心土壁。', 700);
      return;
    }

    player.r = target.r;
    player.c = target.c;

    if (currentLevel === 2) {
      handleLevelTwoPlayerMove();
      requestRender();
      return;
    }

    if (carriedDiscovery) {
      const last = returnTrail[returnTrail.length - 1];
      if (!last || !sameNode(last, player)) returnTrail.push({ r: player.r, c: player.c });
    }

    const food = !carriedDiscovery ? foods.find(f => f.units > 0 && playerTouchesFood(f)) : null;
    if (food && !food.discovered) {
      food.discovered = true;
      discovered += 1;
      carriedDiscovery = food;
      food.routePickupNode = { r: player.r, c: player.c };
      returnTrail = [{ r: player.r, c: player.c }];
      missionTextEl.textContent = '找到食物了！沿你自己的路线回到绿色蚁穴，留下信息素。';
      showToast(`发现 Lv.${food.level || 1} ${food.foodName || '食物'}！把气味带回巢。`);
    }

    if (sameNode(player, nest) && carriedDiscovery) {
      activateRoute(carriedDiscovery, returnTrail);
      carriedDiscovery = null;
      returnTrail = [];
    }
    requestRender();
  }

  function activateRoute(food, playerReturnTrail = []) {
    if (food.routeActivated) return;

    let route = null;
    if (playerReturnTrail.length >= 2) {
      route = playerReturnTrail.slice().reverse();
      if (!sameNode(route[0], nest)) route.unshift({ ...nest });
    } else {
      route = bfsPath(nest, food.routePickupNode || food);
    }

    if (!route || route.length < 2) return;
    food.routeActivated = true;
    food.routePath = route;
    pheromoneRoutes.push({ foodId: food.id, path: route });
    missionTextEl.textContent = '运输线建立！工蚁会沿你刚才走过的路搬食物。继续探索吧。';
    showToast('信息素路线建立，工蚁出发！');
    dispatchWorkers();
  }

  function dispatchWorkers() {
    const activeFoods = foods.filter(f => f.routeActivated && f.units > 0);
    if (!activeFoods.length) return;

    while (workers.length < workerLimit) {
      const food = activeFoods[workers.length % activeFoods.length];
      const routeObj = pheromoneRoutes.find(r => r.foodId === food.id);
      if (!routeObj) break;
      workers.push({
        foodId: food.id,
        path: routeObj.path,
        index: 0,
        direction: 1,
        carrying: false,
        progress: Math.random() * .6,
        speed: .055 + Math.random() * .018
      });
    }
  }

  function updateWorkers(dt) {
    if (scanMode || status !== 'playing') return;
    dispatchWorkers();

    const dead = new Set();
    workers.forEach((w, idx) => {
      const food = foods.find(f => f.id === w.foodId);
      if (!food || (food.units <= 0 && !w.carrying)) {
        dead.add(idx);
        return;
      }

      w.progress += w.speed * dt;
      while (w.progress >= 1) {
        w.progress -= 1;
        w.index += w.direction;

        if (w.direction > 0 && w.index >= w.path.length - 1) {
          w.index = w.path.length - 1;
          if (food.units > 0) {
            food.units -= 1;
            w.carrying = true;
            w.direction = -1;
          } else {
            dead.add(idx);
            return;
          }
        } else if (w.direction < 0 && w.index <= 0) {
          w.index = 0;
          if (w.carrying) {
            storedFood += 1;
            w.carrying = false;
            applyFoodBuff(food);
            maybeGrowColony();
            if (population >= POPULATION_TARGET) {
              completeLevelOne();
              return;
            }
          }

          if (food.units > 0) {
            w.direction = 1;
          } else {
            dead.add(idx);
            return;
          }
        }
      }
    });

    workers = workers.filter((_, i) => !dead.has(i));

  }

  function applyFoodBuff(food) {
    if (food.buffApplied) return;
    food.buffApplied = true;

    if (food.kind === 'cupcake') {
      speedBoostUntil = performance.now() + 15000;
      activeBuffLabel = '🧁 糖分冲刺结束';
      showToast('🧁 糖分冲刺：15秒移动加速！', 2200);
    } else if (food.kind === 'cake') {
      bonusPopulation += 1;
      activeBuffLabel = '🍰 高营养：额外孵化 +1';
      showToast('🍰 高营养！蚁后额外孵化1只。', 2200);
    }
  }

  function maybeGrowColony() {
    const oldPopulation = population;
    population = Math.min(
      POPULATION_TARGET,
      START_POPULATION + Math.floor(storedFood / FOOD_PER_BIRTH) + bonusPopulation
    );
    workerLimit = Math.max(START_POPULATION - 1, population - 1);

    if (population > oldPopulation) {
      const gained = population - oldPopulation;
      showToast(`新蚂蚁出生！人口 +${gained} → ${population}/${POPULATION_TARGET}`, 1900);
      missionTextEl.textContent =
        population >= 7
          ? '蚁穴越来越热闹了。再带回一些食物，就能建立稳定殖民地。'
          : '食物正在变成人口。继续寻找更高等级的食物。';
    }
    updateUI();
  }

  function completeLevelOne() {
    if (status !== 'playing') return;
    status = 'won';
    population = POPULATION_TARGET;
    workerLimit = Math.max(workerLimit, population - 1);
    updateUI();
    gameStateBadge.textContent = '第1关完成';
    gameStateBadge.style.color = '#7bf59a';
    missionTextEl.textContent = '人口达到10只！你已经掌握探索、报信和运输。下一关：搬泥堵住入口，抵御暴雨。';
    level2Unlocked = true;
    setRoadmapActive(1);
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '进入第2关：暴雨来了 →';
    showToast('第1关完成！殖民地诞生了 🐜', 4200);
  }



  function startLevelTwo() {
    if (!qr || !component.length) return;

    currentLevel = 2;
    level2Unlocked = true;
    status = 'playing';
    setLevelTwoUI();
    gameStateBadge.textContent = '第2关 · 暴雨';
    gameStateBadge.style.color = '#5dc8ff';

    foods = [];
    workers = [];
    pheromoneRoutes = [];
    carriedDiscovery = null;
    returnTrail = [];
    speedBoostUntil = 0;
    activeBuffLabel = '';

    player = { ...nest, facing: 'right' };
    entrances = pickLevelTwoEntrances(LEVEL2_ENTRANCE_COUNT);
    mudSources = pickMudSources(2);
    mudWorkers = [];
    carryingMud = false;
    carriedMudSource = null;
    mudTrail = [];
    flooded = new Set();
    floodFrontier = [];
    level2RainStarted = false;
    lastFloodTick = 0;
    level2StartTime = performance.now();
    scanPauseStarted = 0;

    if (entrances.length < LEVEL2_ENTRANCE_COUNT || !mudSources.length) {
      status = 'lost';
      missionTextEl.textContent = '这张二维码没有生成足够的可达施工点，请点击「生成新蚁穴」重新生成。';
      showToast('施工点生成失败，请重新生成蚁穴。', 3200);
      return;
    }

    missionTextEl.textContent = '先找到棕色泥堆，自动扛起一块泥，再送到任意蓝色入口。';
    updateUI(level2StartTime);
    showToast('第2关开始：90秒后暴雨进水！', 2800);
    requestRender();
  }

  function handleLevelTwoPlayerMove() {
    if (carryingMud) {
      const last = mudTrail[mudTrail.length - 1];
      if (!last || !sameNode(last, player)) mudTrail.push({ r: player.r, c: player.c });

      const entrance = entrances.find(e => !e.sealed && sameNode(e, player));
      if (entrance) {
        deliverMudToEntrance(entrance);
        return;
      }
    }

    if (!carryingMud) {
      const source = mudSources.find(s => playerTouchesFood(s));
      if (source) {
        carryingMud = true;
        carriedMudSource = source;
        mudTrail = [{ r: player.r, c: player.c }];
        missionTextEl.textContent = '扛到泥了！把它送到一个蓝色入口。你走的路会变成施工运输线。';
        showToast('🟤 扛起1块泥，送去蓝色入口！', 1800);
      }
    }
  }

  function deliverMudToEntrance(entrance) {
    if (!carryingMud || entrance.sealed) return;

    entrance.progress = Math.min(entrance.required, entrance.progress + 1);

    if (!entrance.route && carriedMudSource && mudTrail.length >= 2) {
      entrance.route = mudTrail.slice();
      if (!sameNode(entrance.route[entrance.route.length - 1], entrance)) {
        entrance.route.push({ r: entrance.r, c: entrance.c });
      }
      entrance.sourceId = carriedMudSource.id;
      showToast('施工路线建立！工蚁开始接力搬泥。', 2100);
    } else {
      showToast(`入口封堵 ${entrance.progress}/${entrance.required}`, 1500);
    }

    carryingMud = false;
    carriedMudSource = null;
    mudTrail = [];

    if (entrance.progress >= entrance.required) {
      sealEntrance(entrance);
    } else {
      dispatchMudWorkers();
      missionTextEl.textContent = '工蚁正在沿施工路线搬泥。你去给另一个入口建立路线。';
    }

    checkLevelTwoComplete();
    updateUI();
  }

  function sealEntrance(entrance) {
    if (entrance.sealed) return;
    entrance.sealed = true;
    entrance.progress = entrance.required;
    showToast('✓ 一个入口封死了！', 1900);
  }

  function dispatchMudWorkers() {
    const activeEntrances = entrances.filter(e => !e.sealed && e.route && e.route.length >= 2);
    if (!activeEntrances.length) return;

    for (const entrance of activeEntrances) {
      const already = mudWorkers.filter(w => w.entranceId === entrance.id).length;
      const desired = Math.min(2, entrance.required - entrance.progress);
      for (let i = already; i < desired && mudWorkers.length < LEVEL2_WORKER_LIMIT; i++) {
        mudWorkers.push({
          entranceId: entrance.id,
          sourceId: entrance.sourceId,
          path: entrance.route,
          index: 0,
          direction: 1,
          carrying: true,
          progress: Math.random() * .35,
          speed: .05 + Math.random() * .014
        });
      }
    }
  }

  function updateMudWorkers(dt) {
    if (scanMode || currentLevel !== 2 || status !== 'playing') return;
    dispatchMudWorkers();

    const dead = new Set();
    mudWorkers.forEach((w, idx) => {
      const entrance = entrances.find(e => e.id === w.entranceId);
      if (!entrance || entrance.sealed) {
        dead.add(idx);
        return;
      }

      w.progress += w.speed * dt;
      while (w.progress >= 1) {
        w.progress -= 1;
        w.index += w.direction;

        if (w.direction > 0 && w.index >= w.path.length - 1) {
          w.index = w.path.length - 1;
          if (w.carrying) {
            entrance.progress = Math.min(entrance.required, entrance.progress + 1);
            w.carrying = false;
            if (entrance.progress >= entrance.required) {
              sealEntrance(entrance);
              dead.add(idx);
              checkLevelTwoComplete();
              return;
            }
          }
          w.direction = -1;
        } else if (w.direction < 0 && w.index <= 0) {
          w.index = 0;
          if (entrance.sealed) {
            dead.add(idx);
            return;
          }
          w.carrying = true;
          w.direction = 1;
        }
      }
    });

    mudWorkers = mudWorkers.filter((_, i) => !dead.has(i));
  }

  function startLevelTwoRain() {
    if (level2RainStarted || status !== 'playing') return;
    level2RainStarted = true;
    gameStateBadge.textContent = '暴雨进水';
    gameStateBadge.style.color = '#5dc8ff';
    missionTextEl.textContent = '暴雨已经进来了！还没封住的入口正在进水，快补最后的泥！';
    showToast('🌧️ 暴雨来了！未封入口开始进水！', 2600);

    for (const entrance of entrances) {
      if (entrance.sealed) continue;
      const k = nodeKey(entrance.r, entrance.c);
      if (!flooded.has(k)) {
        flooded.add(k);
        floodFrontier.push({ r: entrance.r, c: entrance.c });
      }
    }
  }

  function updateLevelTwoFlood(now) {
    if (!level2RainStarted || scanMode || status !== 'playing') return;
    if (now - lastFloodTick < 430) return;
    lastFloodTick = now;

    const expansionBudget = 1;
    let expanded = 0;
    const next = [];

    while (floodFrontier.length && expanded < expansionBudget) {
      const cur = floodFrontier.shift();
      for (const n of graph.get(nodeKey(cur.r, cur.c)) || []) {
        const nk = nodeKey(n.r, n.c);
        if (!componentSet.has(nk) || flooded.has(nk)) continue;
        flooded.add(nk);
        next.push(n);
        expanded += 1;

        if (sameNode(n, nest)) {
          failLevelTwo();
          return;
        }
        if (expanded >= expansionBudget) break;
      }
    }

    floodFrontier.push(...next);
  }

  function updateLevelTwo(now, dt) {
    if (scanMode || status !== 'playing') return;
    updateMudWorkers(dt);

    if (!level2RainStarted && now - level2StartTime >= LEVEL2_SECONDS * 1000) {
      startLevelTwoRain();
    }
    updateLevelTwoFlood(now);
    updateUI(now);
  }

  function checkLevelTwoComplete() {
    if (currentLevel !== 2 || status !== 'playing') return;
    if (entrances.length && entrances.every(e => e.sealed)) completeLevelTwo();
  }

  function completeLevelTwo() {
    if (status !== 'playing') return;
    status = 'won';
    gameStateBadge.textContent = '第2关完成';
    gameStateBadge.style.color = '#7bf59a';
    populationBarEl.style.width = '100%';
    missionTextEl.textContent = '两个入口都封住了，蚁穴撑过暴雨。下一关将解锁 Space 咬击，对付入侵的大蚂蚁。';
    buffTextEl.textContent = '✓ 防洪成功：施工与限时玩法已掌握';
    roadmap2El.classList.add('active');
    roadmap3El.classList.remove('locked');
    roadmap3El.classList.add('unlocked');
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = true;
    nextLevelBtn.textContent = '第3关：入侵者（下一步开发）';
    showToast('第2关完成！蚁穴守住了 🌧️✓', 4200);
  }

  function failLevelTwo() {
    if (status !== 'playing') return;
    status = 'lost';
    gameStateBadge.textContent = '蚁穴进水';
    gameStateBadge.style.color = '#ff7777';
    missionTextEl.textContent = '积水到达蚁穴。下一次先给两个入口都建立施工路线，再让工蚁接力封堵。';
    buffTextEl.textContent = '失败提示：你只需要亲自送第一块泥，后续交给工蚁';
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '重试第2关';
    showToast('蚁穴被淹了，再试一次！', 3200);
  }

  function drawMudSources() {
    const { step } = boardMetrics();
    mudSources.forEach(source => {
      const p = foodScreenPosition(source);
      const s = Math.max(8, step * .58);
      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.shadowColor = 'rgba(113, 67, 34, .35)';
      ctx.shadowBlur = Math.max(3, step * .18);
      ctx.fillStyle = '#8a542f';
      ctx.strokeStyle = '#4d2b18';
      ctx.lineWidth = Math.max(1, step * .055);
      [[-.34,.15,.46],[.15,.08,.5],[.02,-.28,.4]].forEach(([x,y,r]) => {
        ctx.beginPath();
        ctx.arc(x*s, y*s, r*s, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
      });
      ctx.restore();
    });
  }

  function drawEntrances() {
    const { step } = boardMetrics();
    entrances.forEach(entrance => {
      const p = nodeXY(entrance);
      const r = Math.max(9, step * .58);
      ctx.save();
      ctx.lineWidth = Math.max(2, step * .1);

      if (entrance.sealed) {
        ctx.fillStyle = '#8a542f';
        ctx.strokeStyle = '#573019';
        ctx.beginPath();
        ctx.arc(p.x, p.y, r, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
        ctx.fillStyle = '#fff4df';
        ctx.font = `900 ${Math.max(10, step * .5)}px system-ui`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('✓', p.x, p.y + .5);
      } else {
        ctx.fillStyle = 'rgba(93,200,255,.12)';
        ctx.strokeStyle = '#38bfff';
        ctx.beginPath();
        ctx.arc(p.x, p.y, r, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();

        ctx.fillStyle = '#163347';
        ctx.font = `900 ${Math.max(8, step * .34)}px system-ui`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(`${entrance.progress}/${entrance.required}`, p.x, p.y + .4);
      }
      ctx.restore();
    });
  }

  function drawMudWorkers() {
    mudWorkers.forEach(w => {
      const p = workerPosition(w);
      drawAntAt(p.x, p.y, p.angle, '#ff9d35', .82, w.carrying, 'mud');
    });
  }

  function drawFlood() {
    if (!flooded.size) return;
    const { step } = boardMetrics();
    ctx.save();
    flooded.forEach(key => {
      const p = nodeXY(parseKey(key));
      ctx.fillStyle = 'rgba(49, 174, 255, .5)';
      ctx.beginPath();
      ctx.arc(p.x, p.y, Math.max(2.2, step * .18), 0, Math.PI * 2);
      ctx.fill();
    });
    ctx.restore();
  }

  function boardMetrics() {
    const totalModules = matrixSize + QUIET * 2;
    const step = canvas.width / totalModules;
    return { step, offset: QUIET * step };
  }

  function nodeXY(node) {
    const { step, offset } = boardMetrics();
    return { x: offset + node.c * step, y: offset + node.r * step };
  }

  function renderQR(clean = false) {
    ctx.save();
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    const { step, offset } = boardMetrics();
    ctx.fillStyle = clean ? '#000000' : '#191613';

    for (let r = 0; r < matrixSize; r++) {
      for (let c = 0; c < matrixSize; c++) {
        if (!qr.isDark(r, c)) continue;
        const x1 = Math.round(offset + c * step);
        const y1 = Math.round(offset + r * step);
        const x2 = Math.round(offset + (c + 1) * step);
        const y2 = Math.round(offset + (r + 1) * step);
        ctx.fillRect(x1, y1, x2 - x1, y2 - y1);
      }
    }
    ctx.restore();
  }

  function drawPheromones() {
    const { step } = boardMetrics();
    ctx.save();
    ctx.fillStyle = 'rgba(110, 205, 106, .42)';
    pheromoneRoutes.forEach(route => {
      route.path.forEach((node, i) => {
        if (i % 2) return;
        const p = nodeXY(node);
        ctx.beginPath();
        ctx.arc(p.x, p.y, Math.max(1.3, step * .08), 0, Math.PI * 2);
        ctx.fill();
      });
    });
    ctx.restore();
  }

  function drawNest() {
    const { step } = boardMetrics();
    const p = nodeXY(nest);
    ctx.save();
    ctx.lineWidth = Math.max(2, step * .18);
    ctx.strokeStyle = '#38df7b';
    ctx.fillStyle = 'rgba(56, 223, 123, .18)';
    ctx.beginPath();
    ctx.arc(p.x, p.y, Math.max(5, step * .42), 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    ctx.beginPath();
    ctx.arc(p.x, p.y, Math.max(2.5, step * .18), 0, Math.PI * 2);
    ctx.fillStyle = '#38df7b';
    ctx.fill();
    ctx.restore();
  }

  function drawFood(food) {
    if (food.units <= 0) return;

    const { step } = boardMetrics();
    const p = foodScreenPosition(food);
    const icons = {
      donut: '🍩',
      cupcake: '🧁',
      cake: '🍰'
    };
    const icon = icons[food.kind] || '🍩';

    // Real emoji-style food is much easier to recognize at QR scale than a
    // hand-drawn abstract shape. Higher-tier food is also slightly larger.
    const level = food.level || 1;
    const iconSize = Math.max(20, step * (1.16 + level * .09));

    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.font = `${iconSize}px "Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",sans-serif`;

    // Small neutral halo separates the emoji from both black and white modules.
    ctx.shadowColor = 'rgba(255, 176, 82, .55)';
    ctx.shadowBlur = Math.max(5, step * .28);
    ctx.fillText(icon, 0, 0);
    ctx.shadowBlur = 0;

    if (food.discovered) {
      const bx = iconSize * .35;
      const by = -iconSize * .34;
      const br = Math.max(6, step * .24);

      ctx.fillStyle = '#21130c';
      ctx.strokeStyle = level === 3 ? '#ff8ca1' : (level === 2 ? '#ffd27a' : '#e9bd91');
      ctx.lineWidth = Math.max(1.2, step * .055);
      ctx.beginPath();
      ctx.arc(bx, by, br, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();

      ctx.fillStyle = '#fff8ed';
      ctx.font = `800 ${Math.max(8, step * .32)}px system-ui`;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(String(food.units), bx, by + .3);
    }

    ctx.restore();
  }

  function drawAntAt(x, y, angle, color, scale = 1, carrying = false, carryingKind = 'donut') {
    const { step } = boardMetrics();
    const s = Math.max(2.8, step * .245) * scale;
    ctx.save();
    ctx.translate(x, y);
    ctx.rotate(angle);
    ctx.lineCap = 'round';

    ctx.strokeStyle = 'rgba(255,255,255,.82)';
    ctx.lineWidth = Math.max(1, s * .28);
    for (const sign of [-1, 1]) {
      [-.8, 0, .8].forEach(k => {
        ctx.beginPath();
        ctx.moveTo(k * s * .8, sign * s * .2);
        ctx.lineTo(k * s * 1.4, sign * s * 1.1);
        ctx.stroke();
      });
    }

    ctx.fillStyle = color;
    ctx.strokeStyle = 'rgba(29,19,9,.95)';
    ctx.lineWidth = Math.max(.7, s * .22);
    [-.9, 0, .9].forEach(k => {
      ctx.beginPath();
      ctx.arc(k * s, 0, s * (k === 0 ? .62 : .72), 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
    });

    if (carrying) {
      ctx.save();
      ctx.translate(-2.25 * s, 0);
      ctx.rotate(-angle);
      if (carryingKind === 'mud') {
        ctx.fillStyle = '#8a542f';
        ctx.strokeStyle = '#4d2b18';
        ctx.lineWidth = Math.max(.8, s * .12);
        ctx.beginPath();
        ctx.arc(0, 0, s * .82, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
      } else {
        const icons = { donut: '🍩', cupcake: '🧁', cake: '🍰' };
        ctx.font = `${Math.max(10, s * 1.55)}px "Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(icons[carryingKind] || '🍩', 0, 0);
      }
      ctx.restore();
    }
    ctx.restore();
  }

  function facingAngle(dir) {
    return {
      right: 0,
      down: Math.PI / 2,
      left: Math.PI,
      up: -Math.PI / 2
    }[dir] || 0;
  }

  function drawPlayer() {
    const p = nodeXY(player);
    drawAntAt(p.x, p.y, facingAngle(player.facing), '#ffc83d', 1.18, false);

    if (currentLevel === 2 && carryingMud) {
      const { step } = boardMetrics();
      ctx.save();
      ctx.fillStyle = '#8a542f';
      ctx.strokeStyle = '#4d2b18';
      ctx.lineWidth = Math.max(1, step * .05);
      ctx.beginPath();
      ctx.arc(p.x + step * .42, p.y - step * .34, Math.max(5, step * .3), 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.restore();
    }

    if (carriedDiscovery) {
      const { step } = boardMetrics();
      ctx.save();
      ctx.strokeStyle = '#ffc83d';
      ctx.lineWidth = Math.max(1, step * .08);
      ctx.setLineDash([Math.max(2, step * .15), Math.max(2, step * .15)]);
      const n = nodeXY(nest);
      ctx.beginPath();
      ctx.moveTo(p.x, p.y);
      ctx.lineTo(n.x, n.y);
      ctx.stroke();
      ctx.restore();
    }
  }

  function workerPosition(w) {
    const a = w.path[Math.max(0, Math.min(w.path.length - 1, w.index))];
    const nextIndex = Math.max(0, Math.min(w.path.length - 1, w.index + w.direction));
    const b = w.path[nextIndex] || a;
    const pa = nodeXY(a);
    const pb = nodeXY(b);
    return {
      x: pa.x + (pb.x - pa.x) * w.progress,
      y: pa.y + (pb.y - pa.y) * w.progress,
      angle: Math.atan2(pb.y - pa.y, pb.x - pa.x)
    };
  }

  function drawWorkers() {
    workers.forEach(w => {
      const p = workerPosition(w);
      const food = foods.find(f => f.id === w.foodId);
      drawAntAt(p.x, p.y, p.angle, '#ff9d35', .82, w.carrying, food?.kind);
    });
  }


  function render() {
    renderRequest = null;
    if (!qr) return;
    renderQR(scanMode);
    if (scanMode) return;

    if (currentLevel === 2) {
      drawFlood();
      drawMudSources();
      drawEntrances();
      drawNest();
      drawMudWorkers();
      drawPlayer();
      return;
    }

    drawPheromones();
    foods.forEach(drawFood);
    drawNest();
    drawWorkers();
    drawPlayer();
  }

  function requestRender() {
    if (renderRequest) return;
    renderRequest = requestAnimationFrame(render);
  }

  let lastFrame = performance.now();
  function loop(now) {
    const dt = Math.min(2, (now - lastFrame) / 16.6667);
    lastFrame = now;

    if (status === 'playing') {
      if (currentLevel === 2) updateLevelTwo(now, dt);
      else {
        updateWorkers(dt);
        updateUI(now);
      }
    }

    requestRender();
    requestAnimationFrame(loop);
  }

  function handleKey(e) {
    const map = {
      ArrowUp: 'up',
      KeyW: 'up',
      ArrowDown: 'down',
      KeyS: 'down',
      ArrowLeft: 'left',
      KeyA: 'left',
      ArrowRight: 'right',
      KeyD: 'right'
    };

    if (map[e.code]) {
      e.preventDefault();
      movePlayer(map[e.code]);
      return;
    }

    if (e.code === 'Space') {
      e.preventDefault();
      showToast('🦷 咬击会在第3关「入侵者」解锁。', 1500);
    } else if (e.code === 'KeyF') {
      e.preventDefault();
      showToast('💧 蚁酸会在第4关「狩猎」解锁。', 1500);
    }
  }

  document.addEventListener('keydown', handleKey, { passive: false });

  nextLevelBtn.addEventListener('click', () => {
    if (currentLevel === 1 && level2Unlocked) startLevelTwo();
    else if (currentLevel === 2 && status === 'lost') startLevelTwo();
  });

  roadmap2El.addEventListener('click', () => {
    if (level2Unlocked && currentLevel !== 2) startLevelTwo();
  });

  document.querySelectorAll('[data-dir]').forEach(btn => {
    let hold = null;
    const dir = btn.dataset.dir;

    const start = e => {
      e.preventDefault();
      movePlayer(dir);
      clearInterval(hold);
      hold = setInterval(() => movePlayer(dir), 95);
    };

    const stop = () => {
      clearInterval(hold);
      hold = null;
    };

    btn.addEventListener('pointerdown', start);
    btn.addEventListener('pointerup', stop);
    btn.addEventListener('pointercancel', stop);
    btn.addEventListener('pointerleave', stop);
  });

  let swipeStart = null;
  canvas.addEventListener('pointerdown', e => {
    swipeStart = { x: e.clientX, y: e.clientY };
  });

  canvas.addEventListener('pointerup', e => {
    if (!swipeStart) return;
    const dx = e.clientX - swipeStart.x;
    const dy = e.clientY - swipeStart.y;
    swipeStart = null;
    if (Math.hypot(dx, dy) < 18) return;
    if (Math.abs(dx) > Math.abs(dy)) movePlayer(dx > 0 ? 'right' : 'left');
    else movePlayer(dy > 0 ? 'down' : 'up');
  });

  generateBtn.addEventListener('click', () => {
    resetGame(qrInput.value.trim() || 'QR Ant Colony');
  });

  qrInput.addEventListener('keydown', e => {
    if (e.key === 'Enter') resetGame(qrInput.value.trim() || 'QR Ant Colony');
  });

  scanBtn.addEventListener('click', () => {
    const now = performance.now();
    if (!scanMode && currentLevel === 2 && status === 'playing') {
      scanPauseStarted = now;
    } else if (scanMode && currentLevel === 2 && status === 'playing' && scanPauseStarted) {
      level2StartTime += now - scanPauseStarted;
      scanPauseStarted = 0;
    }

    scanMode = !scanMode;
    scanBtn.textContent = scanMode ? '返回游戏' : '扫码模式';
    showToast(scanMode ? '已隐藏游戏元素，可直接扫码；关卡计时暂停。' : '继续探索蚁穴。');
    requestRender();
  });

  resetGame(qrInput.value);
  requestAnimationFrame(loop);
})();