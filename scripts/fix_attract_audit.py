from pathlib import Path
import re

p = Path('game.js')
s = p.read_text(encoding='utf-8')


def replace_once(old, new, label):
    global s
    if old not in s:
        raise SystemExit(f'missing anchor: {label}')
    s = s.replace(old, new, 1)


def replace_block(start_marker, end_marker, new_block, label):
    global s
    start = s.find(start_marker)
    if start < 0:
        raise SystemExit(f'missing block start: {label}')
    end = s.find(end_marker, start)
    if end < 0:
        raise SystemExit(f'missing block end: {label}')
    s = s[:start] + new_block + s[end:]

replace_once(
"""      pause: attractRandom() * 16,
      variant,
      wobble: attractRandom() * Math.PI * 2
    };""",
"""      pause: attractRandom() * 16,
      variant,
      wobble: attractRandom() * Math.PI * 2,
      carrying:
        kind === 'carrier' || kind === 'builder'
          ? direction < 0
          : kind === 'outerCarrier' || kind === 'outerBuilder'
            ? direction > 0
            : false
    };""",
'explicit attract cargo state')

insert_before = "  function repathAttractScout(ant, fromNode) {\n"
pos = s.find(insert_before)
if pos < 0:
    raise SystemExit('missing repathAttractScout insertion point')
area_helpers = r'''  function attractAreaAllows(node, area) {
    if (!node) return false;
    if (area === 'topLeft') return node.r <= matrixSize * .54 && node.c <= matrixSize * .54;
    if (area === 'bottomRight') return node.r >= matrixSize * .46 && node.c >= matrixSize * .46;
    return true;
  }

  function pickAttractAreaNodes(count, area) {
    if (!nest || !component.length) return [];
    const dist = distanceMap(nest);
    const values = [...dist.values()];
    const maxD = values.length ? Math.max(...values) : 1;
    const cutoff = Math.max(5, maxD * .34);
    const pool = component.filter(node => {
      const d = dist.get(nodeKey(node.r, node.c));
      return attractAreaAllows(node, area) && Number.isFinite(d) && d >= cutoff &&
        !isFinderForbiddenNode(node) && !nodeTouchesProtected(node);
    });
    for (let i = pool.length - 1; i > 0; i--) {
      const j = Math.floor(attractRandom() * (i + 1));
      [pool[i], pool[j]] = [pool[j], pool[i]];
    }
    const picked = [];
    const spacing = Math.max(2.5, matrixSize * .065);
    for (const node of pool) {
      if (picked.every(other => Math.hypot(other.r - node.r, other.c - node.c) >= spacing)) {
        picked.push({ ...node });
        if (picked.length >= count) break;
      }
    }
    if (picked.length < count) {
      for (const node of pool) {
        if (picked.length >= count) break;
        if (picked.some(other => sameNode(other, node))) continue;
        picked.push({ ...node });
      }
    }
    return picked;
  }

  function makeAttractAreaRoute(start, area, desiredSteps = 13) {
    if (!start || !nest) return null;
    const dist = distanceMap(nest);
    const values = [...dist.values()];
    const maxD = values.length ? Math.max(...values) : 1;
    const cutoff = Math.max(4, maxD * .28);
    const path = [{ ...start }];
    let current = { ...start };
    let previousKey = null;
    for (let step = 0; step < desiredSteps; step++) {
      let choices = (graph.get(nodeKey(current.r, current.c)) || []).filter(node => {
        const d = dist.get(nodeKey(node.r, node.c));
        return componentSet.has(nodeKey(node.r, node.c)) && attractAreaAllows(node, area) &&
          Number.isFinite(d) && d >= cutoff && !isFinderForbiddenNode(node) && !nodeTouchesProtected(node);
      });
      if (choices.length > 1 && previousKey) {
        const forward = choices.filter(node => nodeKey(node.r, node.c) !== previousKey);
        if (forward.length) choices = forward;
      }
      if (!choices.length) break;
      const next = choices[Math.floor(attractRandom() * choices.length)];
      previousKey = nodeKey(current.r, current.c);
      current = { ...next };
      path.push(current);
    }
    return path.length >= 4 ? path : null;
  }

'''
s = s[:pos] + area_helpers + s[pos:]

new_enter = r'''  function enterAttractMode() {
    if (!qr || !component.length || !nest) return;
    appMode = 'attract';
    status = 'attract';
    scanMode = false;
    scanBtn.textContent = '扫码模式';
    resetAttractRng();

    attractAnts = [];
    attractResources = [];
    attractRoutes = [];
    attractIntruder = null;

    const workNodes = pickAttractNodes(10, false);
    const nearNodes = pickAttractNodes(3, true);
    const peripheralNodes = pickAttractPeripheralNodes(14);
    const topLeftNodes = pickAttractAreaNodes(4, 'topLeft');
    const bottomRightNodes = pickAttractAreaNodes(4, 'bottomRight');
    const foodKinds = ['donut', 'cupcake', 'cake'];

    const addOuterCarrier = (node, route, variant = 0) => {
      if (!node || !route || route.length < 2) return false;
      const displayCell = chooseFoodDisplayCell(node);
      if (!displayCell) return false;
      const foodKind = foodKinds[variant % foodKinds.length];
      const ant = makeAttractAnt('outerCarrier', route, variant);
      if (!ant) return false;
      attractAnts.push(ant);
      attractRoutes.push({ path: route, kind: 'outerFood' });
      attractResources.push({ ...node, kind: 'food', foodKind, displayCell });
      return true;
    };

    const addOuterBuilder = (node, route, variant = 0) => {
      if (!node || !route || route.length < 2) return false;
      const ant = makeAttractAnt('outerBuilder', route, variant);
      if (!ant) return false;
      attractAnts.push(ant);
      attractRoutes.push({ path: route, kind: 'outerMud' });
      attractResources.push({ ...node, kind: 'mud' });
      return true;
    };

    workNodes.slice(0, 3).forEach((node, i) => {
      const path = bfsPath(nest, node);
      const ant = makeAttractAnt('carrier', path, i);
      if (!ant) return;
      attractAnts.push(ant);
      attractRoutes.push({ path, kind: 'food' });
      attractResources.push({ ...node, kind: 'food', foodKind: foodKinds[i % foodKinds.length], displayCell: chooseFoodDisplayCell(node) });
    });

    if (workNodes.length >= 3) {
      const path = makeAttractCrossRoute(workNodes[0], workNodes[2]);
      const ant = makeAttractAnt('crossCarrier', path, 1);
      if (ant) {
        attractAnts.push(ant);
        attractRoutes.push({ path, kind: 'food' });
      }
    }

    workNodes.slice(3, 4).forEach((node, i) => {
      const path = bfsPath(nest, node);
      const ant = makeAttractAnt('builder', path, i);
      if (!ant) return;
      attractAnts.push(ant);
      attractRoutes.push({ path, kind: 'mud' });
      attractResources.push({ ...node, kind: 'mud' });
    });

    peripheralNodes.slice(0, 5).forEach((node, i) => {
      const path = makeAttractPeripheralRoute(node, 13 + (i % 3) * 3);
      const ant = makeAttractAnt('outerScout', path, i);
      if (ant) attractAnts.push(ant);
    });
    peripheralNodes.slice(5, 8).forEach((node, i) => {
      addOuterCarrier(node, makeAttractPeripheralRoute(node, 12 + i * 2), i);
    });
    peripheralNodes.slice(8, 10).forEach((node, i) => {
      addOuterBuilder(node, makeAttractPeripheralRoute(node, 11 + i * 3), i);
    });

    topLeftNodes.slice(0, 2).forEach((node, i) => {
      const path = makeAttractAreaRoute(node, 'topLeft', 12 + i * 3);
      const ant = makeAttractAnt('outerScout', path, 10 + i);
      if (ant) attractAnts.push(ant);
    });
    if (topLeftNodes[2]) addOuterBuilder(topLeftNodes[2], makeAttractAreaRoute(topLeftNodes[2], 'topLeft', 13), 10);

    bottomRightNodes.slice(0, 2).forEach((node, i) => {
      const path = makeAttractAreaRoute(node, 'bottomRight', 13 + i * 3);
      const ant = makeAttractAnt('outerScout', path, 20 + i);
      if (ant) attractAnts.push(ant);
    });
    if (bottomRightNodes[2]) {
      const route = makeAttractAreaRoute(bottomRightNodes[2], 'bottomRight', 15);
      if (!addOuterCarrier(bottomRightNodes[2], route, 2)) {
        const ant = makeAttractAnt('outerScout', route, 22);
        if (ant) attractAnts.push(ant);
      }
    }

    nearNodes.slice(0, 1).forEach((node, i) => {
      const path = bfsPath(nest, node);
      const ant = makeAttractAnt('attendant', path, i);
      if (ant) attractAnts.push(ant);
    });
    nearNodes.slice(1, 3).forEach((node, i) => {
      const path = bfsPath(nest, node);
      const ant = makeAttractAnt('guard', path, i);
      if (ant) attractAnts.push(ant);
    });

    attractNextIntruderAt = performance.now() + 2200 + attractRandom() * 2600;
    document.body.classList.add('attract-mode');
    setAttractUI();
    requestRender();
  }
'''
replace_block('  function enterAttractMode() {', '\n  function enterPlayMode() {', new_enter, 'enterAttractMode')

new_update = r'''  function updateAttractAnt(ant, dt) {
    if (!ant?.path?.length) return;
    if (ant.pause > 0) {
      ant.pause = Math.max(0, ant.pause - dt);
      return;
    }
    ant.wobble += dt * .035;
    const drift = .96 + Math.sin(ant.wobble) * .045;
    ant.speed = ant.baseSpeed * drift;
    ant.progress += ant.speed * dt;
    while (ant.progress >= 1) {
      ant.progress -= 1;
      ant.index += ant.direction;
      const pauseChance = ant.kind === 'scout' || ant.kind === 'outerScout' ? .18 : ant.kind === 'attendant' ? .16 : ant.kind === 'builder' || ant.kind === 'outerBuilder' ? .11 : ant.kind === 'guard' ? .10 : .065;
      if (ant.index > 0 && ant.index < ant.path.length - 1 && attractRandom() < pauseChance) {
        ant.pause = 2 + attractRandom() * 11;
        break;
      }
      if (ant.index >= ant.path.length - 1) {
        ant.index = ant.path.length - 1;
        ant.progress = 0;
        if (ant.kind === 'scout' && repathAttractScout(ant, ant.path[ant.path.length - 1])) break;
        if (ant.kind === 'carrier' || ant.kind === 'builder') ant.carrying = true;
        else ant.carrying = false;
        ant.direction = -1;
        ant.pause = ant.kind === 'attendant' ? 7 + attractRandom() * 20 : 4 + attractRandom() * 17;
        break;
      }
      if (ant.index <= 0) {
        ant.index = 0;
        ant.progress = 0;
        if (ant.kind === 'scout' && repathAttractScout(ant, ant.path[0])) break;
        if (ant.kind === 'outerCarrier' || ant.kind === 'outerBuilder') ant.carrying = true;
        else ant.carrying = false;
        ant.direction = 1;
        ant.pause = ant.kind === 'attendant' ? 6 + attractRandom() * 18 : 3 + attractRandom() * 15;
        break;
      }
    }
  }
'''
replace_block('  function updateAttractAnt(ant, dt) {', '\n  function spawnAttractIntruder(now) {', new_update, 'updateAttractAnt')

new_draw = r'''  function drawAttractAnts() {
    attractAnts.forEach(ant => {
      const p = workerPosition(ant);
      if (ant.kind === 'carrier') {
        const kinds = ['donut', 'cupcake', 'cake'];
        drawAntAt(p.x, p.y, p.angle, '#ff9d35', .80, !!ant.carrying, kinds[ant.variant % kinds.length]);
      } else if (ant.kind === 'crossCarrier') {
        drawAntAt(p.x, p.y, p.angle, '#ffb24b', .79, false);
      } else if (ant.kind === 'builder') {
        drawAntAt(p.x, p.y, p.angle, '#a9663c', .84, !!ant.carrying, 'mud');
      } else if (ant.kind === 'outerCarrier') {
        const kinds = ['donut', 'cupcake', 'cake'];
        drawAntAt(p.x, p.y, p.angle, '#f2a94d', .75, !!ant.carrying, kinds[ant.variant % kinds.length]);
      } else if (ant.kind === 'outerBuilder') {
        drawAntAt(p.x, p.y, p.angle, '#9e6844', .76, !!ant.carrying, 'mud');
      } else if (ant.kind === 'outerScout') {
        drawAntAt(p.x, p.y, p.angle, '#f6cf5f', .70, false);
      } else if (ant.kind === 'guard') {
        drawAntAt(p.x, p.y, p.angle, '#63d99a', .96, false);
      } else if (ant.kind === 'attendant') {
        drawAntAt(p.x, p.y, p.angle, '#e6b36a', .68, false);
      } else {
        drawAntAt(p.x, p.y, p.angle, '#ffd35a', .72, false);
      }
    });
    if (attractIntruder) {
      const p = workerPosition(attractIntruder);
      drawAntAt(p.x, p.y, p.angle, '#ef6256', .90, false);
    }
  }
'''
replace_block('  function drawAttractAnts() {', '\n  function drawAttractScene', new_draw, 'drawAttractAnts')

first = s.find('  function dispatchMudWorkers() {')
second = s.find('  function dispatchMudWorkers() {', first + 1)
if first < 0 or second < 0:
    raise SystemExit('expected duplicate Level 2 dispatchMudWorkers functions')
rain = s.find('  function startLevelTwoRain() {', second)
if rain < 0:
    raise SystemExit('missing startLevelTwoRain after stale duplicate block')
s = s[:second] + s[rain:]

replace_once("""    source.activated = true;
    source.route = route;
    source.routeEfficiency = efficiency;""", """    source.activated = true;
    source.workNode = { ...goal };
    source.route = route;
    source.routeEfficiency = efficiency;""", 'level2 mud workNode')
replace_once("          const target = chooseMudTargetEntrance(source);", "          const target = chooseMudTargetEntrance(source.workNode || source);", 'level2 mud target starts at reported node')
replace_once("          const pathBackToMud = bfsPath(from, source);", "          const pathBackToMud = bfsPath(from, source.workNode || source);", 'level2 path back to reported node')
replace_once("    statLabel2El.textContent = '运输线路';", "    statLabel2El.textContent = '活动线路';", 'attract route label')

p.write_text(s, encoding='utf-8')

funcs = re.findall(r'^\s*function\s+([A-Za-z_$][\w$]*)\s*\(', s, flags=re.M)
dupes = sorted({name for name in funcs if funcs.count(name) > 1})
if dupes:
    raise SystemExit('duplicate function declarations remain: ' + ', '.join(dupes))
if 'Math.random(' in s:
    raise SystemExit('non-seeded Math.random reintroduced')
html = Path('index.html').read_text(encoding='utf-8')
ids = set(re.findall(r'\bid="([^"]+)"', html))
refs = set(re.findall(r"getElementById\('([^']+)'\)", s))
missing = sorted(refs - ids)
if missing:
    raise SystemExit('missing DOM ids: ' + ', '.join(missing))
print(f'audit ok: {len(funcs)} named functions, {len(ids)} html ids, no duplicate functions')
