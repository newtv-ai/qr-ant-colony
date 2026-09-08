(() => {
  'use strict';

  const canvas = document.getElementById('gameCanvas');
  const ctx = canvas.getContext('2d');
  const qrInput = document.getElementById('qrInput');
  const generateBtn = document.getElementById('generateBtn');
  const scanBtn = document.getElementById('scanBtn');
  const foodScoreEl = document.getElementById('foodScore');
  const workerCountEl = document.getElementById('workerCount');
  const rainTimerEl = document.getElementById('rainTimer');
  const discoveredCountEl = document.getElementById('discoveredCount');
  const missionTextEl = document.getElementById('missionText');
  const gameStateBadge = document.getElementById('gameStateBadge');
  const toastEl = document.getElementById('toast');

  const TARGET_FOOD = 12;
  const RAIN_START_SECONDS = 70;
  const QUIET = 4;
  const MOVE_COOLDOWN = 55;

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
  let workerLimit = 3;
  let scanMode = false;
  let status = 'playing';
  let startTime = performance.now();
  let lastMoveTime = 0;
  let rainStarted = false;
  let rainFrontier = [];
  let flooded = new Set();
  let lastFloodTick = 0;
  let toastTimer = null;
  let carriedDiscovery = null;
  let renderRequest = null;

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
    const ordered = component
      .map(n => ({ n, d: dist.get(nodeKey(n.r, n.c)) || 0 }))
      .filter(x => x.d > Math.max(8, matrixSize * .28))
      .sort((a, b) => b.d - a.d);

    const chosen = [];
    for (const item of ordered) {
      if (chosen.every(x => Math.hypot(x.r - item.n.r, x.c - item.n.c) > matrixSize * .18)) {
        chosen.push({ ...item.n });
        if (chosen.length >= count) break;
      }
    }
    while (chosen.length < count && component.length) {
      const n = component[Math.floor(Math.random() * component.length)];
      if (!sameNode(n, nest)) chosen.push({ ...n });
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
    foods = foodNodes.map((node, i) => {
      const big = i % 3 === 0;
      return {
        ...node,
        id: `food-${Date.now()}-${i}`,
        units: big ? 4 : 3,
        maxUnits: big ? 4 : 3,
        kind: big ? 'bread' : (i % 2 === 0 ? 'crumb' : 'sugar'),
        displayCell: chooseFoodDisplayCell(node),
        discovered: false,
        routeActivated: false
      };
    });

    workers = [];
    pheromoneRoutes = [];
    discovered = 0;
    storedFood = 0;
    workerLimit = 3;
    scanMode = false;
    status = 'playing';
    startTime = performance.now();
    lastMoveTime = 0;
    rainStarted = false;
    rainFrontier = [];
    flooded = new Set();
    lastFloodTick = 0;
    carriedDiscovery = null;
    scanBtn.textContent = '扫码模式';
    gameStateBadge.textContent = '探索中';
    gameStateBadge.style.color = '';
    missionTextEl.textContent = '探索蚁穴，找到一块食物。';
    updateUI();
    showToast('新蚁穴生成完成。先去找食物！');
    requestRender();
  }

  function updateUI(now = performance.now()) {
    foodScoreEl.textContent = `${storedFood} / ${TARGET_FOOD}`;
    workerCountEl.textContent = String(workerLimit);
    discoveredCountEl.textContent = String(discovered);
    const elapsed = (now - startTime) / 1000;
    const left = Math.max(0, Math.ceil(RAIN_START_SECONDS - elapsed));
    rainTimerEl.textContent = rainStarted ? '进水中' : `${left}s`;
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
    if (now - lastMoveTime < MOVE_COOLDOWN) return;
    const target = getMoveTarget(dir);
    player.facing = dir;
    lastMoveTime = now;

    if (!target) {
      showToast('这边是实心土壁。', 700);
      return;
    }

    player.r = target.r;
    player.c = target.c;

    const pKey = nodeKey(player.r, player.c);
    if (flooded.has(pKey)) {
      finish(false, '你被积水困住了。');
      return;
    }

    const food = foods.find(f => f.units > 0 && playerTouchesFood(f));
    if (food && !food.discovered) {
      food.discovered = true;
      discovered += 1;
      carriedDiscovery = food;
      missionTextEl.textContent = '已找到食物！现在回到绿色蚁穴，把气味信息带回去。';
      showToast(`发现${food.maxUnits >= 4 ? '大块' : ''}食物！回巢报信。`);
    }

    if (sameNode(player, nest) && carriedDiscovery) {
      activateRoute(carriedDiscovery);
      carriedDiscovery = null;
    }
    requestRender();
  }

  function activateRoute(food) {
    if (food.routeActivated) return;
    const route = bfsPath(nest, food);
    if (!route || route.length < 2) return;
    food.routeActivated = true;
    pheromoneRoutes.push({ foodId: food.id, path: route });
    missionTextEl.textContent = '信息素路线建立。工蚁正在搬运；你可以继续寻找下一块食物。';
    showToast('信息带回蚁穴！工蚁出发。');
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
            maybeGrowColony();
            if (storedFood >= TARGET_FOOD) {
              finish(true, '食物储备完成，蚁群撑过了暴雨季！');
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

    const remainingUndiscovered = foods.some(f => !f.discovered && f.units > 0);
    if (
      !carriedDiscovery &&
      !remainingUndiscovered &&
      foods.every(f => f.units <= 0) &&
      storedFood < TARGET_FOOD
    ) {
      spawnMoreFood(3);
    }
  }

  function maybeGrowColony() {
    const nextLimit = 3 + Math.floor(storedFood / 3);
    if (nextLimit > workerLimit) {
      workerLimit = Math.min(8, nextLimit);
      showToast(`殖民地壮大：工蚁上限 ${workerLimit}`);
    }
    updateUI();
  }

  function spawnMoreFood(count) {
    const nodes = pickFoodNodes(count);
    const base = Date.now();
    nodes.forEach((node, i) => foods.push({
      ...node,
      id: `food-${base}-${i}`,
      units: 3,
      maxUnits: 3,
      kind: i % 2 === 0 ? 'crumb' : 'sugar',
      displayCell: chooseFoodDisplayCell(node),
      discovered: false,
      routeActivated: false
    }));
    showToast('新的食物气味出现在远处。');
  }

  function startRain() {
    if (rainStarted || status !== 'playing') return;
    rainStarted = true;
    gameStateBadge.textContent = '暴雨进水';
    gameStateBadge.style.color = '#5dc8ff';
    missionTextEl.textContent = '暴雨开始！积水正在沿通道逼近蚁穴。';
    showToast('暴雨来了！快把食物搬回来！', 2800);

    const dist = distanceMap(nest);
    const candidates = component
      .filter(n => n.r <= 2 || n.c <= 2 || n.r >= matrixSize - 2 || n.c >= matrixSize - 2)
      .sort(
        (a, b) =>
          (dist.get(nodeKey(b.r, b.c)) || 0) - (dist.get(nodeKey(a.r, a.c)) || 0)
      );

    const start = candidates[0] || component[0];
    if (start) {
      const k = nodeKey(start.r, start.c);
      flooded.add(k);
      rainFrontier = [start];
    }
  }

  function updateRain(now) {
    if (!rainStarted || scanMode || status !== 'playing') return;
    if (now - lastFloodTick < 260) return;
    lastFloodTick = now;

    const next = [];
    const expansionBudget = Math.max(2, Math.floor(matrixSize / 10));
    let added = 0;

    while (rainFrontier.length && added < expansionBudget) {
      const cur = rainFrontier.shift();
      for (const n of graph.get(nodeKey(cur.r, cur.c)) || []) {
        const nk = nodeKey(n.r, n.c);
        if (!componentSet.has(nk) || flooded.has(nk)) continue;
        flooded.add(nk);
        next.push(n);
        added += 1;

        if (sameNode(n, nest)) {
          finish(false, '积水淹进了蚁穴。');
          return;
        }
        if (added >= expansionBudget) break;
      }
    }
    rainFrontier.push(...next);
  }

  function finish(win, message) {
    status = win ? 'won' : 'lost';
    gameStateBadge.textContent = win ? '蚁群存活' : '巢穴失守';
    gameStateBadge.style.color = win ? '#7bf59a' : '#ff7777';
    missionTextEl.textContent = message + ' 点击「生成新蚁穴」再来一局。';
    showToast(win ? '蚁群活下来了！' : '这一窝没守住，再来一次。', 3600);
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
    const kind = food.kind || (food.maxUnits >= 4 ? 'bread' : 'crumb');
    const s = Math.max(10, step * .78);

    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.lineJoin = 'round';
    ctx.lineCap = 'round';
    ctx.shadowColor = 'rgba(255, 157, 59, .48)';
    ctx.shadowBlur = Math.max(3, step * .22);

    if (kind === 'sugar') {
      // A tiny sugar cube: bright enough to read as food, but outlined so it
      // remains visible over the white parts of the QR code.
      ctx.rotate(-Math.PI / 12);
      ctx.fillStyle = '#fff5d8';
      ctx.strokeStyle = '#b76522';
      ctx.lineWidth = Math.max(1.2, step * .075);
      ctx.beginPath();
      ctx.roundRect(-s * .55, -s * .48, s * 1.1, s * .96, s * .13);
      ctx.fill();
      ctx.stroke();

      ctx.shadowBlur = 0;
      ctx.strokeStyle = 'rgba(255,255,255,.9)';
      ctx.lineWidth = Math.max(1, step * .04);
      ctx.beginPath();
      ctx.moveTo(-s * .35, -s * .25);
      ctx.lineTo(s * .22, -s * .25);
      ctx.stroke();
    } else if (kind === 'bread') {
      // Bread chunk: crust outside, soft center inside.
      ctx.fillStyle = '#a94d1e';
      ctx.strokeStyle = '#5f2c13';
      ctx.lineWidth = Math.max(1.1, step * .065);
      ctx.beginPath();
      ctx.moveTo(-s * .72, s * .42);
      ctx.lineTo(-s * .62, -s * .18);
      ctx.quadraticCurveTo(-s * .55, -s * .72, 0, -s * .72);
      ctx.quadraticCurveTo(s * .55, -s * .72, s * .62, -s * .18);
      ctx.lineTo(s * .72, s * .42);
      ctx.closePath();
      ctx.fill();
      ctx.stroke();

      ctx.shadowBlur = 0;
      ctx.fillStyle = '#f5c36d';
      ctx.beginPath();
      ctx.moveTo(-s * .48, s * .28);
      ctx.lineTo(-s * .4, -s * .12);
      ctx.quadraticCurveTo(-s * .34, -s * .48, 0, -s * .5);
      ctx.quadraticCurveTo(s * .34, -s * .48, s * .4, -s * .12);
      ctx.lineTo(s * .48, s * .28);
      ctx.closePath();
      ctx.fill();
    } else {
      // Irregular cookie / bread crumb.
      ctx.fillStyle = '#e98932';
      ctx.strokeStyle = '#7a3517';
      ctx.lineWidth = Math.max(1.1, step * .065);
      ctx.beginPath();
      ctx.moveTo(-s * .58, -s * .16);
      ctx.lineTo(-s * .25, -s * .58);
      ctx.lineTo(s * .28, -s * .5);
      ctx.lineTo(s * .6, -s * .05);
      ctx.lineTo(s * .38, s * .48);
      ctx.lineTo(-s * .18, s * .58);
      ctx.lineTo(-s * .62, s * .22);
      ctx.closePath();
      ctx.fill();
      ctx.stroke();

      ctx.shadowBlur = 0;
      ctx.fillStyle = '#6c2d16';
      [[-.22,-.18],[.18,-.08],[-.02,.25]].forEach(([x,y]) => {
        ctx.beginPath();
        ctx.arc(x * s, y * s, Math.max(1, s * .085), 0, Math.PI * 2);
        ctx.fill();
      });
    }

    // Remaining portions are shown as a tiny badge instead of printing a
    // number over the food illustration.
    if (food.discovered) {
      ctx.shadowBlur = 0;
      ctx.setTransform(1, 0, 0, 1, p.x, p.y);
      const bx = s * .56;
      const by = -s * .56;
      const br = Math.max(5.5, step * .23);
      ctx.fillStyle = '#2b170d';
      ctx.strokeStyle = '#ffd28b';
      ctx.lineWidth = Math.max(1, step * .045);
      ctx.beginPath();
      ctx.arc(bx, by, br, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.fillStyle = '#fff3d7';
      ctx.font = `800 ${Math.max(7, step * .31)}px system-ui`;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(String(food.units), bx, by + .3);
    }

    ctx.restore();
  }

  function drawAntAt(x, y, angle, color, scale = 1, carrying = false) {
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
      ctx.fillStyle = '#ff7826';
      ctx.beginPath();
      ctx.arc(-2.0 * s, 0, s * .72, 0, Math.PI * 2);
      ctx.fill();
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
      drawAntAt(p.x, p.y, p.angle, '#ff9d35', .82, w.carrying);
    });
  }

  function drawFlood() {
    if (!flooded.size) return;
    const { step } = boardMetrics();
    ctx.save();
    flooded.forEach(key => {
      const p = nodeXY(parseKey(key));
      ctx.fillStyle = 'rgba(49, 174, 255, .42)';
      ctx.beginPath();
      ctx.arc(p.x, p.y, Math.max(1.8, step * .14), 0, Math.PI * 2);
      ctx.fill();
    });
    ctx.restore();
  }

  function render() {
    renderRequest = null;
    if (!qr) return;
    renderQR(scanMode);
    if (scanMode) return;
    drawPheromones();
    drawFlood();
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
      const elapsed = (now - startTime) / 1000;
      if (!rainStarted && elapsed >= RAIN_START_SECONDS) startRain();
      updateWorkers(dt);
      updateRain(now);
      updateUI(now);
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
    }
  }

  document.addEventListener('keydown', handleKey, { passive: false });

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
    scanMode = !scanMode;
    scanBtn.textContent = scanMode ? '返回游戏' : '扫码模式';
    showToast(scanMode ? '已隐藏游戏元素，可直接扫码。' : '继续探索蚁穴。');
    requestRender();
  });

  resetGame(qrInput.value);
  requestAnimationFrame(loop);
})();