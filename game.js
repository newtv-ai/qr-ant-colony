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
  const roadmap5El = document.getElementById('roadmap5');
  const roadmap6El = document.getElementById('roadmap6');
  const biteBtn = document.getElementById('biteBtn');
  const acidBtn = document.getElementById('acidBtn');
  const mobileBiteBtn = document.querySelector('[data-mobile-action="bite"]');
  const mobileAcidBtn = document.querySelector('[data-mobile-action="acid"]');
  const scanHealthEl = document.getElementById('scanHealth');
  const shareBtn = document.getElementById('shareBtn');
  const resultOverlayEl = document.getElementById('resultOverlay');
  const resultTitleEl = document.getElementById('resultTitle');
  const resultGradeEl = document.getElementById('resultGrade');
  const resultScoreEl = document.getElementById('resultScore');
  const resultSummaryEl = document.getElementById('resultSummary');
  const shareRunBtn = document.getElementById('shareRunBtn');
  const replayChallengeBtn = document.getElementById('replayChallengeBtn');
  const newWorldBtn = document.getElementById('newWorldBtn');
  const upgradeOverlayEl = document.getElementById('upgradeOverlay');
  const upgradeTitleEl = document.getElementById('upgradeTitle');
  const upgradeSubtitleEl = document.getElementById('upgradeSubtitle');
  const upgradeChoicesEl = document.getElementById('upgradeChoices');

  const POPULATION_TARGET = 10;
  const START_POPULATION = 3;
  const FOOD_PER_BIRTH = 2;
  const QUIET = 4;
  const MOVE_COOLDOWN = 55;
  const BOOSTED_MOVE_COOLDOWN = 45;
  const LEVEL2_SECONDS = 90;
  const LEVEL2_ENTRANCE_COUNT = 2;
  const MUD_REQUIRED_PER_ENTRANCE = 3;
  const LEVEL2_WORKER_LIMIT = 10;
  const LEVEL3_SECONDS = 45;
  const LEVEL3_NEST_HP = 5;
  const BITE_COOLDOWN = 260;
  const GUARD_BASE_COOLDOWN = 950;
  const LEVEL4_SECONDS = 60;
  const LEVEL4_TARGET = 8;
  const ACID_COOLDOWN = 950;
  const ACID_SLOW_MS = 3600;
  const LEVEL5_SECONDS = 75;
  const LEVEL5_TARGET = 8;
  const LEVEL6_SCOUT_SECONDS = 45;
  const MIGRATION_FLOOD_INTERVAL = 520;

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
  let reportedMudSource = null;
  let mudReportTrail = [];
  let mudWorkers = [];
  let mudDiscovered = 0;
  let level2StartTime = 0;
  let level2RainStarted = false;
  let flooded = new Set();
  let floodFrontier = [];
  let lastFloodTick = 0;
  let scanPauseStarted = 0;

  let level3Unlocked = false;
  let enemies = [];
  let enemySpawnNodes = [];
  let level3StartTime = 0;
  let lastEnemySpawn = 0;
  let enemySpawnCount = 0;
  let enemiesDefeated = 0;
  let nestHp = LEVEL3_NEST_HP;
  let lastBiteTime = 0;
  let biteEffectUntil = 0;
  let lastGuardAttack = 0;
  let guardFlashUntil = 0;

  let transportSpeedMultiplier = 1;
  let engineeringSpeedMultiplier = 1;
  let rainTimeBonus = 0;
  let nestHpBonus = 0;
  let biteDamageBonus = 0;
  let guardCount = 0;
  let chosenUpgradeLevels = new Set();
  let chosenUpgradeNames = [];

  let level4Unlocked = false;
  let prey = [];
  let level4StartTime = 0;
  let lastPreySpawn = 0;
  let preyDefeated = 0;
  let lastAcidTime = 0;
  let acidEffectUntil = 0;
  let acidTargets = [];

  let level5Unlocked = false;
  let rivalNest = null;
  let contestStored = 0;
  let rivalStored = 0;
  let rivalWorkers = [];
  let contestWorkerCount = 0;
  let level5StartTime = 0;
  let rivalStartAt = 0;

  let level6Unlocked = false;
  let migrationExit = null;
  let migrationTrail = [];
  let migrationRoute = null;
  let migrationExitFound = false;
  let migrationQueen = null;
  let migrationRaiders = [];
  let migrationFlooded = new Set();
  let migrationFloodFrontier = [];
  let migrationFloodStarted = false;
  let migrationFloodAt = 0;
  let lastMigrationFloodTick = 0;
  let level6StartTime = 0;
  let migrationEfficiency = 1;

  let runSeed = 0;
  let rngState = 0;
  let runScore = 0;
  let levelScoreAwarded = new Set();

  let qrPayload = '';
  let qrSafetyMode = false;
  let qrVerifyFailures = 0;
  let qrVerifySuccesses = 0;
  let lastQrVerifyAt = 0;
  let qrVerifyBusy = false;
  const qrVerifyCanvas = document.createElement('canvas');
  const qrVerifyCtx = qrVerifyCanvas.getContext('2d', { willReadFrequently: true });
  qrVerifyCanvas.width = 420;
  qrVerifyCanvas.height = 420;

  function nodeKey(r, c) { return `${r},${c}`; }
  function parseKey(key) { const [r, c] = key.split(',').map(Number); return { r, c }; }
  function sameNode(a, b) { return a && b && a.r === b.r && a.c === b.c; }

  function hashSeed(text) {
    let h = 2166136261 >>> 0;
    const str = String(text || 'QR Ant Colony');
    for (let i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = Math.imul(h, 16777619);
    }
    return h >>> 0 || 0x6d2b79f5;
  }

  function freshSeed() {
    try {
      const arr = new Uint32Array(1);
      crypto.getRandomValues(arr);
      return arr[0] || hashSeed(Date.now());
    } catch (_) {
      return hashSeed(`${Date.now()}-${performance.now()}`);
    }
  }

  function setRunSeed(seed) {
    const n = Number(seed);
    runSeed = Number.isFinite(n) ? (n >>> 0) : freshSeed();
    if (!runSeed) runSeed = 0x6d2b79f5;
    rngState = runSeed;
  }

  function resetStageRng(level) {
    let mixed = (runSeed ^ Math.imul((level + 17) >>> 0, 0x9e3779b1)) >>> 0;
    mixed ^= mixed >>> 16;
    mixed = Math.imul(mixed, 0x85ebca6b) >>> 0;
    mixed ^= mixed >>> 13;
    rngState = mixed || 0x6d2b79f5;
  }

  function seededRandom() {
    let x = rngState >>> 0;
    x ^= x << 13;
    x ^= x >>> 17;
    x ^= x << 5;
    rngState = x >>> 0 || 0x6d2b79f5;
    return (rngState >>> 0) / 4294967296;
  }

  function challengeUrl() {
    const url = new URL(location.href);
    url.search = '';
    url.hash = '';
    url.searchParams.set('q', qrPayload || qrInput.value.trim() || 'QR Ant Colony');
    url.searchParams.set('s', (runSeed >>> 0).toString(36));
    return url.toString();
  }

  function syncChallengeUrl() {
    try {
      history.replaceState(null, '', challengeUrl());
    } catch (_) {}
  }

  function runGrade() {
    if (runScore >= 9000) return 'S';
    if (runScore >= 7600) return 'A';
    if (runScore >= 6200) return 'B';
    return 'C';
  }

  function awardLevelScore(level, amount) {
    if (levelScoreAwarded.has(level)) return;
    levelScoreAwarded.add(level);
    runScore += Math.max(0, Math.round(amount));
  }

  async function copyText(text) {
    if (navigator.clipboard?.writeText) {
      await navigator.clipboard.writeText(text);
      return;
    }
    const area = document.createElement('textarea');
    area.value = text;
    area.style.position = 'fixed';
    area.style.opacity = '0';
    document.body.appendChild(area);
    area.select();
    document.execCommand('copy');
    area.remove();
  }

  async function shareChallenge(withScore = false) {
    const url = challengeUrl();
    const seedCode = (runSeed >>> 0).toString(36).toUpperCase();
    const scoreText = withScore
      ? `我把蚁群带出了这个二维码世界：${runScore}分 · ${runGrade()}级。你能用同一张地图超过我吗？`
      : '我发现了一张可以玩的二维码世界。地图、资源和事件都固定好了，你能带蚁群活下来吗？';
    const text = `${scoreText}\n挑战码：${seedCode}`;

    try {
      if (navigator.share) {
        await navigator.share({
          title: 'QR Ant Colony · 同地图挑战',
          text,
          url
        });
        return;
      }
      await copyText(`${text}\n${url}`);
      showToast('挑战链接已复制，发给朋友就能玩同一张地图！', 2400);
    } catch (err) {
      if (err?.name !== 'AbortError') {
        try {
          await copyText(`${text}\n${url}`);
          showToast('挑战链接已复制！', 1800);
        } catch (_) {
          showToast('分享失败，请复制浏览器地址。', 1800);
        }
      }
    }
  }

  function showFinalResult() {
    const grade = runGrade();
    resultGradeEl.textContent = grade;
    resultScoreEl.textContent = `${runScore} 分`;
    resultTitleEl.textContent = '大迁徙成功 · 这一代蚁群活下来了';
    resultSummaryEl.textContent =
      `路线效率 ${Math.round(migrationEfficiency * 100)}% · 世界种子 ${(runSeed >>> 0).toString(36).toUpperCase()}。把挑战链接发给朋友，对方会进入同一张二维码地图。`;
    resultOverlayEl.hidden = false;
  }

  function isDark(r, c) {
    return r >= 0 && c >= 0 && r < matrixSize && c < matrixSize && qr.isDark(r, c);
  }

  function isFinderForbiddenNode(node) {
    if (!node) return false;
    const pad = 9;
    const top = node.r <= pad;
    const left = node.c <= pad;
    const right = node.c >= matrixSize - pad;
    const bottom = node.r >= matrixSize - pad;
    return (top && left) || (top && right) || (bottom && left);
  }


  function qrVersion() {
    return Math.max(1, Math.round((matrixSize - 17) / 4));
  }

  function alignmentPatternPositions() {
    const version = qrVersion();
    if (version === 1) return [];

    const numAlign = Math.floor(version / 7) + 2;
    const step = version === 32
      ? 26
      : Math.ceil((version * 4 + numAlign * 2 + 1) / (numAlign * 2 - 2)) * 2;

    const result = new Array(numAlign);
    result[0] = 6;
    for (let i = numAlign - 1, pos = matrixSize - 7; i >= 1; i--, pos -= step) {
      result[i] = pos;
    }
    return result;
  }

  function isProtectedModule(r, c) {
    if (r < 0 || c < 0 || r >= matrixSize || c >= matrixSize) return false;

    // Finder patterns + separators + format information around them.
    if (r <= 8 && c <= 8) return true;
    if (r <= 8 && c >= matrixSize - 9) return true;
    if (r >= matrixSize - 9 && c <= 8) return true;

    // Timing patterns and their immediate format intersections.
    if (r === 6 || c === 6) return true;
    if (r === 8 && (c <= 8 || c >= matrixSize - 8)) return true;
    if (c === 8 && (r <= 8 || r >= matrixSize - 8)) return true;

    // Version information for QR version 7+.
    if (qrVersion() >= 7) {
      if (r <= 5 && c >= matrixSize - 11) return true;
      if (c <= 5 && r >= matrixSize - 11) return true;
    }

    // Alignment patterns (5x5), excluding areas already occupied by finders.
    const centers = alignmentPatternPositions();
    for (const ar of centers) {
      for (const ac of centers) {
        const overlapsFinder =
          (ar === 6 && ac === 6) ||
          (ar === 6 && ac === matrixSize - 7) ||
          (ar === matrixSize - 7 && ac === 6);
        if (overlapsFinder) continue;
        if (Math.abs(r - ar) <= 2 && Math.abs(c - ac) <= 2) return true;
      }
    }

    // Fixed dark module.
    if (r === 4 * qrVersion() + 9 && c === 8) return true;
    return false;
  }

  function nodeTouchesProtected(node) {
    return [
      [node.r - 1, node.c - 1],
      [node.r - 1, node.c],
      [node.r, node.c - 1],
      [node.r, node.c]
    ].some(([r, c]) => isProtectedModule(r, c));
  }

  function drawQRProtection() {
    if (!qr || scanMode) return;
    const { step, offset } = boardMetrics();

    ctx.save();

    // Critical QR function modules are always restored exactly after all game
    // graphics, so sprites can never cover finder/timing/alignment structures.
    for (let r = 0; r < matrixSize; r++) {
      for (let c = 0; c < matrixSize; c++) {
        if (!isProtectedModule(r, c)) continue;
        const x1 = Math.round(offset + c * step);
        const y1 = Math.round(offset + r * step);
        const x2 = Math.round(offset + (c + 1) * step);
        const y2 = Math.round(offset + (r + 1) * step);
        ctx.fillStyle = isDark(r, c) ? '#000000' : '#ffffff';
        ctx.fillRect(x1, y1, x2 - x1, y2 - y1);
      }
    }

    // Keep a clean black sampling core in every non-critical dark module.
    // This preserves the QR's center samples while leaving most of each module
    // available for the ant-game overlay.
    const coreRatio = qrSafetyMode ? .58 : .42;
    const core = step * coreRatio;
    ctx.fillStyle = '#000000';
    for (let r = 0; r < matrixSize; r++) {
      for (let c = 0; c < matrixSize; c++) {
        if (!isDark(r, c) || isProtectedModule(r, c)) continue;
        const cx = offset + (c + .5) * step;
        const cy = offset + (r + .5) * step;
        ctx.fillRect(cx - core / 2, cy - core / 2, core, core);
      }
    }

    ctx.restore();
  }

  function setScanHealth(state, text) {
    if (!scanHealthEl) return;
    scanHealthEl.className = `scan-health ${state}`;
    scanHealthEl.textContent = text;
  }

  function verifyGameplayQR() {
    if (!qr || scanMode || qrVerifyBusy || typeof jsQR !== 'function') return;
    qrVerifyBusy = true;

    try {
      qrVerifyCtx.fillStyle = '#fff';
      qrVerifyCtx.fillRect(0, 0, qrVerifyCanvas.width, qrVerifyCanvas.height);
      qrVerifyCtx.drawImage(canvas, 0, 0, qrVerifyCanvas.width, qrVerifyCanvas.height);
      const image = qrVerifyCtx.getImageData(0, 0, qrVerifyCanvas.width, qrVerifyCanvas.height);
      const decoded = jsQR(image.data, image.width, image.height, {
        inversionAttempts: 'dontInvert'
      });

      const ok = !!decoded && decoded.data === qrPayload;
      if (ok) {
        qrVerifyFailures = 0;
        qrVerifySuccesses += 1;
        setScanHealth(
          'good',
          qrSafetyMode ? '✓ 游戏画面可扫码 · 增强保护' : '✓ 游戏画面可扫码'
        );
      } else {
        qrVerifySuccesses = 0;
        qrVerifyFailures += 1;

        if (!qrSafetyMode) {
          qrSafetyMode = true;
          setScanHealth('checking', '正在增强二维码保护...');
          requestRender();
        } else if (qrVerifyFailures >= 2) {
          setScanHealth('warn', '⚠ 当前画面建议用扫码模式');
        }
      }
    } catch (err) {
      setScanHealth('warn', '⚠ 扫码检测暂不可用');
    } finally {
      qrVerifyBusy = false;
    }
  }

  function maybeVerifyGameplayQR(now) {
    if (scanMode || !qr || status === 'lost') return;
    if (typeof jsQR !== 'function') {
      if (now - lastQrVerifyAt > 3000) {
        lastQrVerifyAt = now;
        setScanHealth('warn', '⚠ 扫码检测器未加载');
      }
      return;
    }
    const interval = qrSafetyMode ? 1100 : 1600;
    if (now - lastQrVerifyAt < interval) return;
    lastQrVerifyAt = now;
    verifyGameplayQR();
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

        if (isFinderForbiddenNode({ r, c })) {
          neighbors.set(nodeKey(r, c), []);
          continue;
        }

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
            list.filter(n =>
              n.r > 0 && n.c > 0 &&
              n.r < size - 1 && n.c < size - 1 &&
              !isFinderForbiddenNode(n)
            )
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
      n =>
        n.r > 4 && n.c > 4 &&
        n.r < matrixSize - 4 && n.c < matrixSize - 4 &&
        !nodeTouchesProtected(n)
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
      const j = Math.floor(seededRandom() * (i + 1));
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
      !isDark(cell.r, cell.c) &&
      !isProtectedModule(cell.r, cell.c)
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
    const unlocked = [
      true,
      level2Unlocked,
      level3Unlocked,
      level4Unlocked,
      level5Unlocked,
      level6Unlocked
    ];

    [roadmap1El, roadmap2El, roadmap3El, roadmap4El, roadmap5El, roadmap6El]
      .forEach((el, i) => {
        if (!el) return;
        const n = i + 1;
        el.classList.toggle('active', n === level);
        el.classList.toggle('unlocked', !!unlocked[i]);
        el.classList.toggle('locked', !unlocked[i]);
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
    biteBtn.disabled = true;
    biteBtn.classList.remove('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = true;
      mobileBiteBtn.classList.remove('ready');
    }
    acidBtn.disabled = true;
    acidBtn.classList.remove('ready');
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = true;
      mobileAcidBtn.classList.remove('ready');
    }
    setRoadmapActive(1);
  }

  function setLevelTwoUI() {
    chapterNumberEl.textContent = '第 2 关';
    chapterTitleEl.textContent = '暴雨来了';
    chapterDescEl.textContent =
      `${level2DurationSeconds()}秒内发现泥土并回巢报信。10只工蚁会沿你的信息素路线赶去搬泥。`;
    statLabel1El.textContent = '封堵入口';
    statLabel2El.textContent = '发现泥堆';
    statLabel3El.textContent = '工蚁数量';
    statLabel4El.textContent = '暴雨倒计时';
    legendCardEl.innerHTML = `
      <h2>图例与规则</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：负责探索和报信</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>10只工蚁：全部参与搬泥${engineeringSpeedMultiplier > 1 ? ' · 工程专精' : ''}</span></div>
      <div class="legend"><span style="font-size:17px">🟤</span><span>泥堆：碰到即发现，随后回巢报信</span></div>
      <div class="legend"><span style="color:#5dc8ff;font-size:18px">◎</span><span>入口：每个需要3块泥</span></div>
      <div class="legend"><span class="legend-water"></span><span>积水：倒计时结束后涌入</span></div>
      <div class="legend"><span class="legend-nest"></span><span>蚁穴：不能被水淹到</span></div>
    `;
    nextLevelBtn.hidden = true;
    biteBtn.disabled = true;
    biteBtn.classList.remove('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = true;
      mobileBiteBtn.classList.remove('ready');
    }
    acidBtn.disabled = true;
    acidBtn.classList.remove('ready');
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = true;
      mobileAcidBtn.classList.remove('ready');
    }
    setRoadmapActive(2);
  }

  function setLevelThreeUI() {
    chapterNumberEl.textContent = '第 3 关';
    chapterTitleEl.textContent = '入侵者';
    chapterDescEl.textContent = '守住45秒。敌对大蚂蚁会从二维码边缘冲向蚁穴；Space /「咬」进行近战拦截。';
    statLabel1El.textContent = '蚁穴生命';
    statLabel2El.textContent = '击退敌蚁';
    statLabel3El.textContent = '场上敌蚁';
    statLabel4El.textContent = '守住时间';
    legendCardEl.innerHTML = `
      <h2>一眼看懂</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：黄色守卫蚁</span></div>
      <div class="legend"><span style="color:#f05a4f;font-size:17px">🐜</span><span>红色敌蚁：冲向蚁穴</span></div>
      <div class="legend"><span style="font-size:17px">🦷</span><span>Space / 咬：伤害 ${1 + biteDamageBonus}</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>守卫蚁：${guardCount}只 · 自动保护蚁穴</span></div>
      <div class="legend"><span class="legend-nest"></span><span>蚁穴：生命归零则失败</span></div>
    `;
    nextLevelBtn.hidden = true;
    biteBtn.disabled = false;
    biteBtn.classList.add('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = false;
      mobileBiteBtn.classList.add('ready');
    }
    acidBtn.disabled = true;
    acidBtn.classList.remove('ready');
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = true;
      mobileAcidBtn.classList.remove('ready');
    }
    setRoadmapActive(3);
  }

  function setLevelFourUI() {
    chapterNumberEl.textContent = '第 4 关';
    chapterTitleEl.textContent = '狩猎';
    chapterDescEl.textContent =
      `60秒内猎杀${LEVEL4_TARGET}只甲虫。Space近身咬击，F喷射蚁酸可远程减速猎物。`;
    statLabel1El.textContent = '狩猎目标';
    statLabel2El.textContent = '已猎杀';
    statLabel3El.textContent = '场上猎物';
    statLabel4El.textContent = '剩余时间';
    legendCardEl.innerHTML = `
      <h2>图例与规则</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：黄色猎手蚁</span></div>
      <div class="legend"><span style="font-size:17px">🪲</span><span>甲虫：会在二维码通道里逃窜</span></div>
      <div class="legend"><span style="font-size:17px">🦷</span><span>Space / 咬：近距离造成伤害</span></div>
      <div class="legend"><span style="font-size:17px">💧</span><span>F / 蚁酸：远程减速3.6秒</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>高效路线与进化继续影响后续</span></div>
    `;
    nextLevelBtn.hidden = true;
    biteBtn.disabled = false;
    biteBtn.classList.add('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = false;
      mobileBiteBtn.classList.add('ready');
    }
    acidBtn.disabled = false;
    acidBtn.classList.add('ready');
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = false;
      mobileAcidBtn.classList.add('ready');
    }
    setRoadmapActive(4);
  }

  function setLevelFiveUI() {
    chapterNumberEl.textContent = '第 5 关';
    chapterTitleEl.textContent = '争夺食物';
    chapterDescEl.textContent =
      `75秒资源竞赛。先找到食物并回巢报信，让10只工蚁运输；红色敌群会同时抢夺。`;
    statLabel1El.textContent = '我方食物';
    statLabel2El.textContent = '敌方食物';
    statLabel3El.textContent = '我方工蚁';
    statLabel4El.textContent = '剩余时间';
    legendCardEl.innerHTML = `
      <h2>图例与规则</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：探索、报信、拦截</span></div>
      <div class="legend"><span class="legend-ant worker-ant"></span><span>我方10只工蚁：沿信息素运输</span></div>
      <div class="legend"><span style="color:#ef6256;font-size:17px">🐜</span><span>红色敌蚁：会抢走同一批食物</span></div>
      <div class="legend"><span>🍩</span><span>共享食物：谁先搬走就归谁</span></div>
      <div class="legend"><span style="font-size:17px">💧</span><span>F蚁酸：减速敌方运输蚁</span></div>
      <div class="legend"><span style="font-size:17px">🦷</span><span>Space咬击：可赶跑敌方运输蚁</span></div>
    `;
    nextLevelBtn.hidden = true;
    biteBtn.disabled = false;
    biteBtn.classList.add('ready');
    acidBtn.disabled = false;
    acidBtn.classList.add('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = false;
      mobileBiteBtn.classList.add('ready');
    }
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = false;
      mobileAcidBtn.classList.add('ready');
    }
    setRoadmapActive(5);
  }

  function setLevelSixUI() {
    chapterNumberEl.textContent = '第 6 关';
    chapterTitleEl.textContent = '大迁徙';
    chapterDescEl.textContent =
      '先找到远处的迁徙出口，再回巢带蚁后出发。洪水会从旧巢后方追来，敌蚁还会堵路。';
    statLabel1El.textContent = '迁徙阶段';
    statLabel2El.textContent = '路线效率';
    statLabel3El.textContent = '拦路敌蚁';
    statLabel4El.textContent = '侦察时间';
    legendCardEl.innerHTML = `
      <h2>图例与规则</h2>
      <div class="legend"><span class="legend-ant player-ant"></span><span>你：先探路，再护送蚁后</span></div>
      <div class="legend"><span style="color:#d9c2ff;font-size:17px">●</span><span>蚁后：必须安全抵达出口</span></div>
      <div class="legend"><span style="color:#75d7ff;font-size:18px">◎</span><span>迁徙出口：先找到，再回巢报信</span></div>
      <div class="legend"><span class="legend-water"></span><span>洪水：迁徙开始后从旧巢追来</span></div>
      <div class="legend"><span style="color:#ef6256;font-size:17px">🐜</span><span>拦路敌蚁：会卡住蚁后路线</span></div>
      <div class="legend"><span style="font-size:17px">🦷💧</span><span>咬击 + 蚁酸：清路与减速</span></div>
    `;
    nextLevelBtn.hidden = true;
    biteBtn.disabled = false;
    biteBtn.classList.add('ready');
    acidBtn.disabled = false;
    acidBtn.classList.add('ready');
    if (mobileBiteBtn) {
      mobileBiteBtn.disabled = false;
      mobileBiteBtn.classList.add('ready');
    }
    if (mobileAcidBtn) {
      mobileAcidBtn.disabled = false;
      mobileAcidBtn.classList.add('ready');
    }
    setRoadmapActive(6);
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
      const j = Math.floor(seededRandom() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }


  function routeEfficiency(route, start, goal) {
    if (!route || route.length < 2) return 1;
    const shortest = bfsPath(start, goal);
    if (!shortest || shortest.length < 2) return 1;
    return Math.max(.35, Math.min(1, shortest.length / route.length));
  }

  function routeSpeedFactor(efficiency = 1) {
    return .58 + Math.max(.35, Math.min(1, efficiency)) * .42;
  }

  function level2DurationSeconds() {
    return LEVEL2_SECONDS + rainTimeBonus;
  }

  function level3MaxNestHp() {
    return LEVEL3_NEST_HP + nestHpBonus;
  }

  function latestUpgradeName() {
    return chosenUpgradeNames.length ? chosenUpgradeNames[chosenUpgradeNames.length - 1] : '';
  }

  function upgradeOptionsForLevel(level) {
    if (level === 1) {
      return [
        {
          id: 'trail',
          icon: '🟢',
          title: '信息素专家',
          text: '运输蚁沿你留下的路线移动更快。',
          effect: '后续所有搬运速度 +18%'
        },
        {
          id: 'engineer',
          icon: '🟤',
          title: '工程蚁训练',
          text: '10只工蚁仍都会搬泥，其中一部分接受工程训练。',
          effect: '第二关施工速度 +25% · 暴雨延后10秒'
        },
        {
          id: 'guard',
          icon: '🛡️',
          title: '预备兵蚁',
          text: '从工蚁中训练一只兼任守卫，第二关仍参与搬运。',
          effect: '第三关 +1守卫蚁 · 蚁穴生命 +1'
        }
      ];
    }

    if (level === 2) {
      return [
        {
          id: 'bite',
          icon: '🦷',
          title: '强壮上颚',
          text: '你的近战咬击更致命。',
          effect: '第三关咬击伤害 +1'
        },
        {
          id: 'guards',
          icon: '🐜',
          title: '守巢兵蚁',
          text: '两只蚂蚁接受兵蚁训练，自动驻守蚁穴附近。',
          effect: '第三关 +2自动守卫'
        },
        {
          id: 'fortify',
          icon: '🏠',
          title: '加固蚁穴',
          text: '用第二关剩下的泥加固巢壁。',
          effect: '第三关蚁穴生命 +2'
        }
      ];
    }

    return [];
  }

  function applyUpgrade(level, id) {
    if (chosenUpgradeLevels.has(level)) return;

    let label = '';
    if (id === 'trail') {
      transportSpeedMultiplier *= 1.18;
      label = '信息素专家';
    } else if (id === 'engineer') {
      engineeringSpeedMultiplier *= 1.25;
      rainTimeBonus += 10;
      label = '工程蚁训练';
    } else if (id === 'guard') {
      guardCount += 1;
      nestHpBonus += 1;
      label = '预备兵蚁';
    } else if (id === 'bite') {
      biteDamageBonus += 1;
      label = '强壮上颚';
    } else if (id === 'guards') {
      guardCount += 2;
      label = '守巢兵蚁';
    } else if (id === 'fortify') {
      nestHpBonus += 2;
      label = '加固蚁穴';
    }

    chosenUpgradeLevels.add(level);
    if (label) chosenUpgradeNames.push(label);
    upgradeOverlayEl.hidden = true;

    if (level === 1) {
      missionTextEl.textContent = `蚁群完成进化：${label}。现在进入暴雨关，10只工蚁会继续为你工作。`;
      buffTextEl.textContent = `蚁群专精：${label}`;
      nextLevelBtn.hidden = false;
      nextLevelBtn.disabled = false;
      nextLevelBtn.textContent = '进入第2关：暴雨来了 →';
    } else if (level === 2) {
      missionTextEl.textContent = `蚁群完成进化：${label}。准备迎战入侵者。`;
      buffTextEl.textContent = `蚁群专精：${label}`;
      nextLevelBtn.hidden = false;
      nextLevelBtn.disabled = false;
      nextLevelBtn.textContent = '进入第3关：入侵者 →';
    }

    showToast(`进化完成：${label}`, 2200);
  }

  function showUpgradeSelection(level) {
    if (chosenUpgradeLevels.has(level)) return;
    const options = upgradeOptionsForLevel(level);
    if (!options.length) return;

    upgradeTitleEl.textContent = level === 1 ? '第一次蚁群进化' : '第二次蚁群进化';
    upgradeSubtitleEl.textContent =
      level === 1
        ? '选一个发展方向。它会直接影响后面的暴雨和入侵关卡。'
        : '根据前两关的玩法，决定你的殖民地怎样准备战斗。';

    upgradeChoicesEl.innerHTML = '';
    options.forEach(option => {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'upgrade-choice';
      btn.innerHTML = `
        <span class="icon">${option.icon}</span>
        <strong>${option.title}</strong>
        <small>${option.text}</small>
        <em>${option.effect}</em>
      `;
      btn.addEventListener('click', () => applyUpgrade(level, option.id));
      upgradeChoicesEl.appendChild(btn);
    });

    upgradeOverlayEl.hidden = false;
  }

  function pickLevelTwoEntrances(count) {
    const dist = distanceMap(nest);
    const candidates = shuffled(component.filter(n => {
      const nearEdge = n.r <= 2 || n.c <= 2 || n.r >= matrixSize - 2 || n.c >= matrixSize - 2;
      const d = dist.get(nodeKey(n.r, n.c));
      return nearEdge && Number.isFinite(d) && d >= Math.max(10, matrixSize * .22) && !isFinderZoneNode(n) && !nodeTouchesProtected(n);
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
        !isFinderZoneNode(n) && !nodeTouchesProtected(n) &&
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
          displayCell: cell,
          units: 2,
          maxUnits: 2,
          discovered: false,
          activated: false,
          route: null
        });
        usedCells.add(ck);
        if (chosen.length >= count) break;
      }
    }

    if (chosen.length < count) {
      for (const n of candidates) {
        if (chosen.length >= count) break;
        if (chosen.some(s => sameNode(s, n))) continue;
        const cell = chooseFoodDisplayCell(n);
        if (!cell) continue;
        const ck = nodeKey(cell.r, cell.c);
        if (usedCells.has(ck)) continue;
        chosen.push({
          ...n,
          id: `mud-${chosen.length}-${Date.now()}`,
          displayCell: cell,
          units: 2,
          maxUnits: 2,
          discovered: false,
          activated: false,
          route: null
        });
        usedCells.add(ck);
      }
    }

    return chosen;
  }

  function resetGame(content, seed = null, updateAddress = true) {
    if (typeof qrcode !== 'function') {
      showToast('二维码库加载失败，请检查网络后刷新。', 3200);
      return;
    }

    qrPayload = content || 'QR Ant Colony';
    setRunSeed(seed == null ? freshSeed() : seed);
    resetStageRng(1);
    qrSafetyMode = false;
    qrVerifyFailures = 0;
    qrVerifySuccesses = 0;
    lastQrVerifyAt = 0;
    setScanHealth('checking', '正在检测游戏画面...');

    qr = qrcode(0, 'H');
    qr.addData(qrPayload);
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
      const j = Math.floor(seededRandom() * (i + 1));
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
    level2Unlocked = false;
    level3Unlocked = false;
    level4Unlocked = false;
    level5Unlocked = false;
    level6Unlocked = false;
    transportSpeedMultiplier = 1;
    engineeringSpeedMultiplier = 1;
    rainTimeBonus = 0;
    nestHpBonus = 0;
    biteDamageBonus = 0;
    guardCount = 0;
    chosenUpgradeLevels = new Set();
    chosenUpgradeNames = [];
    lastGuardAttack = 0;
    guardFlashUntil = 0;
    upgradeOverlayEl.hidden = true;
    resultOverlayEl.hidden = true;
    runScore = 0;
    levelScoreAwarded = new Set();
    workers = [];
    pheromoneRoutes = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    reportedMudSource = null;
    mudReportTrail = [];
    mudDiscovered = 0;
    flooded = new Set();
    floodFrontier = [];
    level2RainStarted = false;
    level2StartTime = 0;
    lastFloodTick = 0;
    enemies = [];
    enemySpawnNodes = [];
    level3StartTime = 0;
    lastEnemySpawn = 0;
    enemySpawnCount = 0;
    enemiesDefeated = 0;
    nestHp = LEVEL3_NEST_HP;
    lastBiteTime = 0;
    biteEffectUntil = 0;
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
    showToast(`第1关：第一顿饭 · 世界种子 ${(runSeed >>> 0).toString(36).toUpperCase()}`, 2800);
    if (updateAddress) syncChallengeUrl();
    requestRender();
  }

  function updateUI(now = performance.now()) {
    if (currentLevel === 6) {
      const scoutLeft = Math.max(0, Math.ceil(LEVEL6_SCOUT_SECONDS - (now - level6StartTime)/1000));
      const phase = migrationQueen ? '护送蚁后' : (migrationExitFound ? '返回旧巢' : '寻找出口');
      populationCountEl.textContent = phase;
      foodScoreEl.textContent = `${Math.round(migrationEfficiency*100)}%`;
      workerCountEl.textContent = String(migrationRaiders.length);
      if (!migrationQueen) {
        discoveredCountEl.textContent = `${scoutLeft}s`;
        populationBarEl.style.width = migrationExitFound ? '50%' : '12%';
      } else {
        const progress = migrationQueen.path.length > 1
          ? ((migrationQueen.index + migrationQueen.progress) / (migrationQueen.path.length - 1)) * 100
          : 0;
        populationBarEl.style.width = `${Math.min(100,progress)}%`;
        discoveredCountEl.textContent = migrationFloodStarted
          ? '洪水追赶'
          : `${Math.max(0,Math.ceil((migrationFloodAt-now)/1000))}s后洪水`;
      }
      buffTextEl.textContent = migrationQueen
        ? (migrationPathBlocked()
            ? '⚠ 蚁后被拦路敌蚁卡住了，快去清路'
            : '👑 护送中：路线越高效，蚁后迁徙越快')
        : (migrationExitFound
            ? '已记录迁徙路线：现在回绿色旧巢'
            : '你走出去的路径会成为整个蚁群的迁徙路线');
      return;
    }

    if (currentLevel === 5) {
      const left = Math.max(0,Math.ceil(LEVEL5_SECONDS-(now-level5StartTime)/1000));
      populationCountEl.textContent = `${contestStored} / ${LEVEL5_TARGET}`;
      foodScoreEl.textContent = `${rivalStored} / ${LEVEL5_TARGET}`;
      workerCountEl.textContent = String(contestWorkerCount || LEVEL2_WORKER_LIMIT);
      discoveredCountEl.textContent = `${left}s`;
      populationBarEl.style.width = `${Math.min(100,(contestStored/LEVEL5_TARGET)*100)}%`;
      buffTextEl.textContent = carriedDiscovery
        ? '🍩 已发现食物：立刻回巢报信'
        : rivalWorkers.length
          ? `⚔️ 红色运输蚁 ${rivalWorkers.length}只 · F减速 / Space拦截`
          : '抢先发现食物并建立高效运输线';
      return;
    }

    if (currentLevel === 4) {
      const left = Math.max(0,Math.ceil(LEVEL4_SECONDS-(now-level4StartTime)/1000));
      populationCountEl.textContent = `${preyDefeated} / ${LEVEL4_TARGET}`;
      foodScoreEl.textContent = String(preyDefeated);
      workerCountEl.textContent = String(prey.length);
      discoveredCountEl.textContent = `${left}s`;
      populationBarEl.style.width = `${Math.min(100,(preyDefeated/LEVEL4_TARGET)*100)}%`;
      const acidLeft = Math.max(0,Math.ceil((ACID_COOLDOWN-(now-lastAcidTime))/100)/10);
      buffTextEl.textContent = acidLeft > 0
        ? `💧 蚁酸冷却 ${acidLeft.toFixed(1)}s · 先减速再咬`
        : '💧 蚁酸就绪 · F远程减速，Space近身咬击';
      return;
    }

    if (currentLevel === 3) {
      const left = Math.max(0, Math.ceil(LEVEL3_SECONDS - (now - level3StartTime) / 1000));
      populationCountEl.textContent = `${nestHp} / ${level3MaxNestHp()}`;
      foodScoreEl.textContent = String(enemiesDefeated);
      workerCountEl.textContent = String(enemies.length);
      discoveredCountEl.textContent = `${left}s`;
      populationBarEl.style.width = `${Math.max(0, (nestHp / level3MaxNestHp()) * 100)}%`;
      buffTextEl.textContent =
        `🦷 咬击伤害 ${1 + biteDamageBonus} · 守卫蚁 ${guardCount} · 面向敌人近身攻击`;
      return;
    }

    if (currentLevel === 2) {
      const sealed = entrances.filter(e => e.sealed).length;
      populationCountEl.textContent = `${sealed} / ${entrances.length || LEVEL2_ENTRANCE_COUNT}`;
      foodScoreEl.textContent = `${mudDiscovered} / ${mudSources.length || 3}`;
      workerCountEl.textContent = String(LEVEL2_WORKER_LIMIT);
      const left = Math.max(0, Math.ceil(level2DurationSeconds() - (now - level2StartTime) / 1000));
      discoveredCountEl.textContent = level2RainStarted ? '进水中' : `${left}s`;
      populationBarEl.style.width = `${entrances.length ? (sealed / entrances.length) * 100 : 0}%`;
      buffTextEl.textContent = reportedMudSource
        ? '🟤 已发现泥土：现在回绿色蚁穴报信'
        : mudWorkers.length
          ? `🐜 ${mudWorkers.length}只工蚁正在搬泥${latestUpgradeName() ? ` · 专精：${latestUpgradeName()}` : ''}`
          : `找到泥土 → 回巢报信 → 10只工蚁出发搬运${latestUpgradeName() ? ` · 专精：${latestUpgradeName()}` : ''}`;
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

    if (currentLevel === 5) {
      handleLevelFivePlayerMove();
      requestRender();
      return;
    }

    if (currentLevel === 6) {
      handleLevelSixPlayerMove();
      requestRender();
      return;
    }

    if (currentLevel >= 3) {
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
    const goal = food.routePickupNode || food;
    if (playerReturnTrail.length >= 2) {
      route = playerReturnTrail.slice().reverse();
      if (!sameNode(route[0], nest)) route.unshift({ ...nest });
    } else {
      route = bfsPath(nest, goal);
    }

    if (!route || route.length < 2) return;
    const efficiency = routeEfficiency(route, nest, goal);
    const pct = Math.round(efficiency * 100);

    food.routeActivated = true;
    food.routePath = route;
    food.routeEfficiency = efficiency;
    pheromoneRoutes.push({ foodId: food.id, path: route, efficiency });
    missionTextEl.textContent =
      `运输线建立！路线效率 ${pct}%。路线越短，工蚁搬运越快。`;
    showToast(`信息素路线效率 ${pct}% · 工蚁出发！`, 2100);
    dispatchWorkers();
  }

  function dispatchWorkers() {
    const activeFoods = foods.filter(f => f.routeActivated && f.units > 0);
    if (!activeFoods.length) return;

    while (workers.length < workerLimit) {
      const food = activeFoods[workers.length % activeFoods.length];
      const routeObj = pheromoneRoutes.find(r => r.foodId === food.id);
      if (!routeObj) break;
      const baseSpeed = .055 + seededRandom() * .018;
      workers.push({
        foodId: food.id,
        path: routeObj.path,
        index: 0,
        direction: 1,
        carrying: false,
        progress: seededRandom() * .6,
        routeEfficiency: routeObj.efficiency || 1,
        baseSpeed,
        speed: baseSpeed * routeSpeedFactor(routeObj.efficiency || 1) * transportSpeedMultiplier
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
    missionTextEl.textContent = '人口达到10只！先选择一次蚁群进化，再进入暴雨关。';
    const activeRoutes = pheromoneRoutes.filter(r => Number.isFinite(r.efficiency));
    const avgRoute = activeRoutes.length
      ? activeRoutes.reduce((sum,r) => sum + r.efficiency, 0) / activeRoutes.length
      : 1;
    awardLevelScore(1, 1000 + avgRoute * 520);
    level2Unlocked = true;
    setRoadmapActive(1);
    nextLevelBtn.hidden = true;
    showToast('第1关完成！选择蚁群进化方向 🐜', 2600);
    showUpgradeSelection(1);
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

    resetStageRng(2);
    player = { ...nest, facing: 'right' };
    population = POPULATION_TARGET;
    workerLimit = LEVEL2_WORKER_LIMIT;
    entrances = pickLevelTwoEntrances(LEVEL2_ENTRANCE_COUNT);
    mudSources = pickMudSources(3);
    mudWorkers = [];
    reportedMudSource = null;
    mudReportTrail = [];
    mudDiscovered = 0;
    flooded = new Set();
    floodFrontier = [];
    level2RainStarted = false;
    lastFloodTick = 0;
    level2StartTime = performance.now();
    scanPauseStarted = 0;

    if (entrances.length < LEVEL2_ENTRANCE_COUNT || mudSources.length < 3) {
      status = 'lost';
      missionTextEl.textContent = '这张二维码没有生成足够的可达施工点，请点击「生成新蚁穴」重新生成。';
      showToast('施工点生成失败，请重新生成蚁穴。', 3200);
      return;
    }

    missionTextEl.textContent = '先去寻找棕色泥堆。碰到泥堆后不要自己搬，回绿色蚁穴报信。';
    updateUI(level2StartTime);
    showToast(`第2关开始：${level2DurationSeconds()}秒后暴雨！找到泥土后回巢报信。`, 3000);
    requestRender();
  }

  function handleLevelTwoPlayerMove() {
    if (reportedMudSource) {
      const last = mudReportTrail[mudReportTrail.length - 1];
      if (!last || !sameNode(last, player)) {
        mudReportTrail.push({ r: player.r, c: player.c });
      }

      if (sameNode(player, nest)) {
        activateMudSource(reportedMudSource, mudReportTrail);
        reportedMudSource = null;
        mudReportTrail = [];
      }
      return;
    }

    const source = mudSources.find(
      s => s.units > 0 && !s.discovered && playerTouchesFood(s)
    );
    if (!source) return;

    source.discovered = true;
    mudDiscovered += 1;
    reportedMudSource = source;
    source.reportNode = { r: player.r, c: player.c };
    mudReportTrail = [{ r: player.r, c: player.c }];
    missionTextEl.textContent = '发现泥土了！像第一关发现食物一样，现在回绿色蚁穴把位置告诉工蚁。';
    showToast('🟤 发现泥堆！回巢报信，喊工蚁来搬。', 2200);
  }

  function activateMudSource(source, playerReturnTrail = []) {
    if (!source || source.activated) return;

    let route = null;
    const goal = source.reportNode || source;
    if (playerReturnTrail.length >= 2) {
      route = playerReturnTrail.slice().reverse();
      if (!sameNode(route[0], nest)) route.unshift({ ...nest });
    } else {
      route = bfsPath(nest, goal);
    }

    if (!route || route.length < 2) return;

    const efficiency = routeEfficiency(route, nest, goal);
    const pct = Math.round(efficiency * 100);
    source.activated = true;
    source.route = route;
    source.routeEfficiency = efficiency;
    showToast(`🐜 报信成功！施工路线效率 ${pct}%`, 2400);
    missionTextEl.textContent =
      `10只工蚁已经赶往泥堆。当前施工路线效率 ${pct}%，你继续寻找下一处泥土。`;
    dispatchMudWorkers();
  }

  function chooseMudTargetEntrance(fromNode) {
    const open = entrances.filter(e => !e.sealed && e.progress < e.required);
    if (!open.length) return null;

    let best = null;
    for (const entrance of open) {
      const path = bfsPath(fromNode, entrance);
      if (!path) continue;
      const score = entrance.progress * 1000 + path.length;
      if (!best || score < best.score) best = { entrance, path, score };
    }
    return best;
  }

  function activeMudSourceWithUnits() {
    const active = mudSources.filter(s => s.activated && s.units > 0);
    if (!active.length) return null;
    active.sort((a, b) => b.units - a.units);
    return active[0];
  }

  function dispatchMudWorkers() {
    if (currentLevel !== 2 || status !== 'playing') return;
    const source = activeMudSourceWithUnits();
    if (!source) return;

    while (mudWorkers.length < LEVEL2_WORKER_LIMIT) {
      const baseSpeed = .05 + seededRandom() * .015;
      mudWorkers.push({
        sourceId: source.id,
        entranceId: null,
        path: source.route || bfsPath(nest, source),
        index: 0,
        direction: 1,
        carrying: false,
        progress: seededRandom() * .22,
        baseSpeed,
        speed:
          baseSpeed *
          routeSpeedFactor(source.routeEfficiency || 1) *
          transportSpeedMultiplier *
          engineeringSpeedMultiplier,
        phase: 'toMud'
      });
    }
  }

  function updateMudWorkers(dt) {
    if (scanMode || currentLevel !== 2 || status !== 'playing') return;
    dispatchMudWorkers();

    const dead = new Set();

    mudWorkers.forEach((w, idx) => {
      if (!w.path || w.path.length < 2) {
        dead.add(idx);
        return;
      }

      w.progress += w.speed * dt;

      while (w.progress >= 1) {
        w.progress -= 1;
        w.index += 1;

        if (w.index < w.path.length - 1) continue;

        if (w.phase === 'toMud') {
          const source = mudSources.find(s => s.id === w.sourceId);
          if (!source || source.units <= 0) {
            dead.add(idx);
            return;
          }

          const target = chooseMudTargetEntrance(source);
          if (!target) {
            dead.add(idx);
            return;
          }

          source.units -= 1;
          w.carrying = true;
          w.entranceId = target.entrance.id;
          w.path = target.path;
          w.index = 0;
          w.progress = 0;
          w.phase = 'toEntrance';
          continue;
        }

        if (w.phase === 'toEntrance') {
          let entrance = entrances.find(e => e.id === w.entranceId);

          if (!entrance || entrance.sealed) {
            const currentNode = w.path[w.path.length - 1];
            const reroute = chooseMudTargetEntrance(currentNode);
            if (reroute) {
              w.entranceId = reroute.entrance.id;
              w.path = reroute.path;
              w.index = 0;
              w.progress = 0;
              continue;
            }

            dead.add(idx);
            return;
          }

          entrance.progress = Math.min(entrance.required, entrance.progress + 1);
          if (entrance.progress >= entrance.required) sealEntrance(entrance);

          w.carrying = false;
          checkLevelTwoComplete();
          if (status !== 'playing') {
            dead.add(idx);
            return;
          }

          const source = activeMudSourceWithUnits();
          if (!source) {
            dead.add(idx);
            return;
          }

          const from = entrance || w.path[w.path.length - 1];
          const pathBackToMud = bfsPath(from, source);
          if (!pathBackToMud || pathBackToMud.length < 2) {
            dead.add(idx);
            return;
          }

          w.sourceId = source.id;
          w.entranceId = null;
          w.speed =
            (w.baseSpeed || .055) *
            routeSpeedFactor(source.routeEfficiency || 1) *
            transportSpeedMultiplier *
            engineeringSpeedMultiplier;
          w.path = pathBackToMud;
          w.index = 0;
          w.progress = 0;
          w.phase = 'toMud';
        }
      }
    });

    mudWorkers = mudWorkers.filter((_, i) => !dead.has(i));

    if (
      !reportedMudSource &&
      mudWorkers.length === 0 &&
      mudSources.some(s => !s.discovered && s.units > 0) &&
      entrances.some(e => !e.sealed)
    ) {
      missionTextEl.textContent = '这批泥搬完了。继续探索，找到下一处棕色泥堆并回巢报信。';
    }
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
          progress: seededRandom() * .35,
          speed: .05 + seededRandom() * .014
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

    if (!level2RainStarted && now - level2StartTime >= level2DurationSeconds() * 1000) {
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
    missionTextEl.textContent = '两个入口都封住了。选择第二次蚁群进化，决定第三关怎么防守。';
    const left = Math.max(
      0,
      Math.ceil(level2DurationSeconds() - (performance.now() - level2StartTime) / 1000)
    );
    awardLevelScore(2, 1050 + left * 11);
    buffTextEl.textContent = `✓ 防洪成功 · 当前总分 ${runScore}`;
    level3Unlocked = true;
    setRoadmapActive(2);
    nextLevelBtn.hidden = true;
    showToast('第2关完成！选择战斗进化方向 🌧️✓', 2600);
    showUpgradeSelection(2);
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
      if (source.units <= 0) return;
      const p = foodScreenPosition(source);
      const s = Math.max(10, step * .66);

      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.shadowColor = source.discovered
        ? 'rgba(255, 188, 78, .5)'
        : 'rgba(113, 67, 34, .38)';
      ctx.shadowBlur = Math.max(4, step * .24);
      ctx.fillStyle = '#8a542f';
      ctx.strokeStyle = source.discovered ? '#ffc05b' : '#4d2b18';
      ctx.lineWidth = Math.max(1.2, step * .065);

      [[-.34,.15,.46],[.15,.08,.5],[.02,-.28,.4]].forEach(([x,y,r]) => {
        ctx.beginPath();
        ctx.arc(x*s, y*s, r*s, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
      });
      ctx.shadowBlur = 0;

      if (source.discovered) {
        const br = Math.max(6, step * .24);
        ctx.fillStyle = '#21130c';
        ctx.strokeStyle = '#ffd089';
        ctx.lineWidth = Math.max(1, step * .05);
        ctx.beginPath();
        ctx.arc(s * .52, -s * .42, br, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
        ctx.fillStyle = '#fff4df';
        ctx.font = `800 ${Math.max(8, step * .31)}px system-ui`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(String(source.units), s * .52, -s * .42 + .2);
      }

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


  function pickEnemySpawnNodes(count) {
    const dist = distanceMap(nest);
    const candidates = shuffled(component.filter(n => {
      const nearEdge = n.r <= 2 || n.c <= 2 || n.r >= matrixSize - 2 || n.c >= matrixSize - 2;
      const d = dist.get(nodeKey(n.r, n.c));
      return nearEdge && Number.isFinite(d) && d >= Math.max(10, matrixSize * .2) && !isFinderZoneNode(n) && !nodeTouchesProtected(n);
    }));

    const chosen = [];
    for (const n of candidates) {
      if (chosen.every(e => Math.hypot(e.r - n.r, e.c - n.c) >= matrixSize * .28)) {
        chosen.push({ ...n });
        if (chosen.length >= count) break;
      }
    }
    if (!chosen.length && candidates.length) chosen.push({ ...candidates[0] });
    return chosen;
  }

  function startLevelThree() {
    if (!qr || !component.length) return;

    currentLevel = 3;
    level3Unlocked = true;
    status = 'playing';
    setLevelThreeUI();
    gameStateBadge.textContent = '第3关 · 入侵';
    gameStateBadge.style.color = '#ff7777';

    foods = [];
    workers = [];
    pheromoneRoutes = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    flooded = new Set();
    reportedMudSource = null;
    resetStageRng(3);
    player = { ...nest, facing: 'right' };

    enemies = [];
    enemySpawnNodes = pickEnemySpawnNodes(3);
    enemySpawnCount = 0;
    enemiesDefeated = 0;
    nestHp = level3MaxNestHp();
    lastEnemySpawn = 0;
    lastBiteTime = 0;
    biteEffectUntil = 0;
    lastGuardAttack = 0;
    guardFlashUntil = 0;
    level3StartTime = performance.now();
    lastEnemySpawn = level3StartTime;
    scanPauseStarted = 0;

    if (!enemySpawnNodes.length) {
      status = 'lost';
      missionTextEl.textContent = '这张二维码没有找到合适的敌蚁入口，请重新生成蚁穴。';
      showToast('敌蚁入口生成失败，请重新生成。', 2800);
      return;
    }

    missionTextEl.textContent =
      guardCount > 0
        ? `敌蚁正在逼近。你负责前线咬击，${guardCount}只守卫蚁会自动保护蚁穴附近。`
        : '敌蚁会直奔绿色蚁穴。站到它们前面，面向敌人按 Space 咬击。';
    updateUI(level3StartTime);
    showToast('第3关开始：守住45秒！Space 咬击已解锁 🦷', 3000);
    spawnEnemy();
    requestRender();
  }

  function spawnEnemy() {
    if (currentLevel !== 3 || status !== 'playing' || !enemySpawnNodes.length) return;
    const spawn = enemySpawnNodes[enemySpawnCount % enemySpawnNodes.length];
    const path = bfsPath(spawn, nest);
    if (!path || path.length < 2) return;

    enemySpawnCount += 1;
    const big = enemySpawnCount % 5 === 0;
    enemies.push({
      id: `enemy-${Date.now()}-${enemySpawnCount}`,
      path,
      index: 0,
      direction: 1,
      progress: 0,
      speed: big ? .026 : (.036 + seededRandom() * .008),
      hp: big ? 4 : 2,
      maxHp: big ? 4 : 2,
      big
    });
  }

  function enemyPosition(enemy) {
    const a = enemy.path[Math.max(0, Math.min(enemy.path.length - 1, enemy.index))];
    const b = enemy.path[Math.max(0, Math.min(enemy.path.length - 1, enemy.index + 1))] || a;
    const pa = nodeXY(a);
    const pb = nodeXY(b);
    return {
      x: pa.x + (pb.x - pa.x) * enemy.progress,
      y: pa.y + (pb.y - pa.y) * enemy.progress,
      angle: Math.atan2(pb.y - pa.y, pb.x - pa.x)
    };
  }

  function entityPosition(entity) {
    if (entity?.node && (!entity.path || entity.path.length < 2)) {
      const p = nodeXY(entity.node);
      return { x: p.x, y: p.y, angle: 0 };
    }
    return enemyPosition(entity);
  }

  function randomPlayableNode(origin = null, minDistance = 0) {
    const pool = component.filter(n =>
      !isFinderForbiddenNode(n) &&
      !nodeTouchesProtected(n) &&
      (!origin || Math.hypot(n.r - origin.r, n.c - origin.c) >= minDistance)
    );
    if (!pool.length) return component[Math.floor(seededRandom() * component.length)] || nest;
    return pool[Math.floor(seededRandom() * pool.length)];
  }

  function roamPathFrom(start) {
    for (let tries = 0; tries < 12; tries++) {
      const target = randomPlayableNode(start, Math.max(5, matrixSize * .18));
      const path = bfsPath(start, target);
      if (path && path.length >= 4) return path;
    }
    return bfsPath(start, nest) || [{ ...start }, { ...nest }];
  }

  function startLevelFour() {
    if (!qr || !component.length) return;

    currentLevel = 4;
    level4Unlocked = true;
    status = 'playing';
    resetStageRng(4);
    setLevelFourUI();
    gameStateBadge.textContent = '第4关 · 狩猎';
    gameStateBadge.style.color = '#8ad5ff';

    foods = [];
    workers = [];
    pheromoneRoutes = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    enemies = [];
    flooded = new Set();
    player = { ...nest, facing: 'right' };

    prey = [];
    preyDefeated = 0;
    lastPreySpawn = 0;
    lastAcidTime = 0;
    acidEffectUntil = 0;
    acidTargets = [];
    level4StartTime = performance.now();
    scanPauseStarted = 0;

    for (let i = 0; i < 4; i++) spawnPrey();
    lastPreySpawn = level4StartTime;

    missionTextEl.textContent =
      '甲虫会沿二维码通道逃窜。F先喷蚁酸减速，再靠近用Space咬击。';
    updateUI(level4StartTime);
    showToast('第4关：狩猎开始！F 蚁酸已解锁 💧', 3000);
    requestRender();
  }

  function spawnPrey() {
    if (currentLevel !== 4 || status !== 'playing') return;
    const start = randomPlayableNode(player || nest, Math.max(7, matrixSize * .16));
    const path = roamPathFrom(start);
    if (!path || path.length < 2) return;

    const ordinal = preyDefeated + prey.length + 1;
    const big = ordinal % 4 === 0;
    prey.push({
      id: `prey-${runSeed}-${ordinal}-${Math.floor(seededRandom() * 1e6)}`,
      path,
      index: 0,
      progress: seededRandom() * .45,
      speed: big ? .028 : (.038 + seededRandom() * .010),
      hp: big ? 3 : 2,
      maxHp: big ? 3 : 2,
      big,
      slowedUntil: 0
    });
  }

  function updatePrey(now, dt) {
    prey.forEach(item => {
      const slow = now < (item.slowedUntil || 0) ? .35 : 1;
      item.progress += item.speed * slow * dt;

      while (item.progress >= 1) {
        item.progress -= 1;
        item.index += 1;

        if (item.index >= item.path.length - 1) {
          const current = item.path[item.path.length - 1];
          const nextPath = roamPathFrom(current);
          item.path = nextPath;
          item.index = 0;
          item.progress = 0;
          break;
        }
      }
    });
  }

  function updateLevelFour(now, dt) {
    if (scanMode || status !== 'playing') return;

    updatePrey(now, dt);

    const spawnInterval = 4200;
    if (prey.length < 5 && now - lastPreySpawn >= spawnInterval) {
      spawnPrey();
      lastPreySpawn = now;
    }

    if (preyDefeated >= LEVEL4_TARGET) {
      completeLevelFour(now);
      return;
    }

    const elapsed = now - level4StartTime;
    if (elapsed >= LEVEL4_SECONDS * 1000) {
      failLevelFour();
      return;
    }

    updateUI(now);
  }

  function completeLevelFour(now = performance.now()) {
    if (status !== 'playing') return;
    status = 'won';
    const left = Math.max(0, Math.ceil(LEVEL4_SECONDS - (now - level4StartTime) / 1000));
    awardLevelScore(4, 1200 + left * 12 + preyDefeated * 55);
    level5Unlocked = true;
    gameStateBadge.textContent = '第4关完成';
    gameStateBadge.style.color = '#7bf59a';
    missionTextEl.textContent =
      '狩猎成功。下一关，两窝蚂蚁会争夺同一批食物：路线效率和战斗都要用上。';
    buffTextEl.textContent = `✓ 猎杀 ${preyDefeated} · 当前总分 ${runScore}`;
    setRoadmapActive(4);
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '进入第5关：争夺食物 →';
    showToast('第4关完成！你已经掌握蚁酸狩猎 💧✓', 3600);
  }

  function failLevelFour() {
    if (status !== 'playing') return;
    status = 'lost';
    gameStateBadge.textContent = '狩猎失败';
    gameStateBadge.style.color = '#ff7777';
    missionTextEl.textContent =
      `时间到了，只猎到${preyDefeated}/${LEVEL4_TARGET}。先用F减速，不要一直追着高速甲虫跑。`;
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '重试第4关';
    showToast('猎物跑掉了，再试一次！', 2600);
  }

  function drawPrey() {
    const now = performance.now();
    prey.forEach(item => {
      const p = entityPosition(item);
      const slowed = now < (item.slowedUntil || 0);

      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.rotate(p.angle);
      const { step } = boardMetrics();
      const s = Math.max(6, step * (item.big ? .46 : .36));

      ctx.fillStyle = slowed ? '#69c9db' : (item.big ? '#744d2d' : '#9a6839');
      ctx.strokeStyle = '#2f1c0f';
      ctx.lineWidth = Math.max(1, step * .055);
      ctx.beginPath();
      ctx.ellipse(0, 0, s * 1.05, s * .7, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();

      ctx.fillStyle = slowed ? '#9be9f5' : '#c78d4d';
      ctx.beginPath();
      ctx.ellipse(s * .65, 0, s * .48, s * .5, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();

      for (const sign of [-1, 1]) {
        for (const x of [-.55, 0, .55]) {
          ctx.beginPath();
          ctx.moveTo(x * s, sign * s * .42);
          ctx.lineTo((x + .12) * s, sign * s * 1.05);
          ctx.stroke();
        }
      }
      ctx.restore();

      if (item.hp < item.maxHp || item.big) {
        const { step } = boardMetrics();
        const w = Math.max(14, step * .9);
        const h = Math.max(2, step * .09);
        ctx.save();
        ctx.fillStyle = 'rgba(45,16,12,.72)';
        ctx.fillRect(p.x - w/2, p.y - step * .65, w, h);
        ctx.fillStyle = '#ffb95d';
        ctx.fillRect(p.x - w/2, p.y - step * .65, w * (item.hp / item.maxHp), h);
        ctx.restore();
      }
    });
  }

  function acidAttack() {
    if (currentLevel < 4 || currentLevel > 6 || status !== 'playing' || scanMode) {
      if (currentLevel < 4) showToast('💧 蚁酸会在第4关「狩猎」解锁。', 1400);
      return;
    }

    const now = performance.now();
    if (now - lastAcidTime < ACID_COOLDOWN) return;
    lastAcidTime = now;
    acidEffectUntil = now + 220;

    const pp = nodeXY(player);
    const facing = {
      right: [1, 0],
      left: [-1, 0],
      down: [0, 1],
      up: [0, -1]
    }[player.facing] || [1, 0];
    const { step } = boardMetrics();
    const range = Math.max(58, step * 5.2);

    const targets =
      currentLevel === 4 ? prey :
      currentLevel === 5 ? rivalWorkers :
      currentLevel === 6 ? migrationRaiders :
      [];

    const hits = [];
    targets.forEach(entity => {
      const ep = entityPosition(entity);
      const dx = ep.x - pp.x;
      const dy = ep.y - pp.y;
      const d = Math.hypot(dx, dy);
      if (d > range) return;
      const dot = d < .01 ? 1 : (dx / d) * facing[0] + (dy / d) * facing[1];
      if (dot < .05) return;
      hits.push({ entity, d });
    });

    hits.sort((a, b) => a.d - b.d);
    acidTargets = hits.slice(0, 3).map(hit => hit.entity);
    acidTargets.forEach(entity => {
      entity.slowedUntil = now + ACID_SLOW_MS;
    });

    showToast(
      acidTargets.length
        ? `💧 蚁酸命中${acidTargets.length}个目标 · 减速3.6秒`
        : '蚁酸喷空了',
      850
    );
    requestRender();
  }

  function drawAcidEffect() {
    if (performance.now() > acidEffectUntil) return;
    const p = nodeXY(player);
    const { step } = boardMetrics();
    const angle = facingAngle(player.facing);

    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(angle);
    ctx.fillStyle = 'rgba(81, 214, 219, .16)';
    ctx.strokeStyle = 'rgba(103, 238, 232, .82)';
    ctx.lineWidth = Math.max(1.5, step * .08);
    ctx.beginPath();
    ctx.moveTo(0, 0);
    ctx.arc(0, 0, Math.max(50, step * 5), -.36, .36);
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
    ctx.restore();
  }



  function pickRivalNest() {
    const candidates = component.filter(n =>
      !isFinderForbiddenNode(n) &&
      !nodeTouchesProtected(n) &&
      Math.hypot(n.r - nest.r, n.c - nest.c) >= Math.max(10, matrixSize * .42)
    );
    if (!candidates.length) return randomPlayableNode(nest, Math.max(8, matrixSize * .3));
    return candidates[Math.floor(seededRandom() * candidates.length)];
  }

  function startLevelFive() {
    if (!qr || !component.length) return;

    currentLevel = 5;
    level5Unlocked = true;
    status = 'playing';
    resetStageRng(5);
    setLevelFiveUI();
    gameStateBadge.textContent = '第5关 · 争夺';
    gameStateBadge.style.color = '#ff9b88';

    player = { ...nest, facing: 'right' };
    enemies = [];
    prey = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    flooded = new Set();

    rivalNest = pickRivalNest();
    const nodes = pickFoodNodes(3);
    const kinds = [
      { kind:'donut', name:'甜甜圈' },
      { kind:'cupcake', name:'杯子蛋糕' },
      { kind:'cake', name:'草莓蛋糕' }
    ];

    foods = nodes.map((node, i) => ({
      ...node,
      id: `contest-${runSeed}-${i}`,
      units: 5,
      maxUnits: 5,
      kind: kinds[i % kinds.length].kind,
      foodName: kinds[i % kinds.length].name,
      level: i + 1,
      displayCell: chooseFoodDisplayCell(node),
      discovered: false,
      routeActivated: false,
      routePath: null,
      routeEfficiency: 1
    }));

    workers = [];
    pheromoneRoutes = [];
    carriedDiscovery = null;
    returnTrail = [];
    contestStored = 0;
    rivalStored = 0;
    rivalWorkers = [];
    contestWorkerCount = LEVEL2_WORKER_LIMIT;
    level5StartTime = performance.now();
    rivalStartAt = level5StartTime + 8000;
    lastAcidTime = 0;
    acidEffectUntil = 0;
    scanPauseStarted = 0;

    missionTextEl.textContent =
      '先抢在红色敌群前找到食物并回巢报信。8秒后敌群开始搬运。';
    updateUI(level5StartTime);
    showToast('第5关开始：8秒后敌群加入争夺！', 2800);
    requestRender();
  }

  function handleLevelFivePlayerMove() {
    if (carriedDiscovery) {
      const last = returnTrail[returnTrail.length - 1];
      if (!last || !sameNode(last, player)) returnTrail.push({ r:player.r, c:player.c });
    }

    const food = !carriedDiscovery
      ? foods.find(f => f.units > 0 && !f.discovered && playerTouchesFood(f))
      : null;

    if (food) {
      food.discovered = true;
      carriedDiscovery = food;
      food.routePickupNode = { r:player.r, c:player.c };
      returnTrail = [{ r:player.r, c:player.c }];
      missionTextEl.textContent =
        '发现共享食物！立刻回绿色蚁穴报信，路线越短我方搬得越快。';
      showToast(`抢先发现${food.foodName}！快回巢报信。`, 1700);
    }

    if (sameNode(player, nest) && carriedDiscovery) {
      activateContestRoute(carriedDiscovery, returnTrail);
      carriedDiscovery = null;
      returnTrail = [];
    }
  }

  function activateContestRoute(food, playerReturnTrail = []) {
    if (!food || food.routeActivated) return;
    const goal = food.routePickupNode || food;
    let route = null;

    if (playerReturnTrail.length >= 2) {
      route = playerReturnTrail.slice().reverse();
      if (!sameNode(route[0], nest)) route.unshift({ ...nest });
    } else {
      route = bfsPath(nest, goal);
    }

    if (!route || route.length < 2) return;
    const efficiency = routeEfficiency(route, nest, goal);

    food.routeActivated = true;
    food.routePath = route;
    food.routeEfficiency = efficiency;
    pheromoneRoutes.push({ foodId:food.id, path:route, efficiency });

    missionTextEl.textContent =
      `我方运输线建立：效率${Math.round(efficiency * 100)}%。继续找下一处食物或去拦截红色敌蚁。`;
    showToast('10只工蚁开始抢运食物！', 1800);
    dispatchContestWorkers();
  }

  function dispatchContestWorkers() {
    const active = foods.filter(f => f.routeActivated && f.units > 0);
    if (!active.length) return;

    while (workers.length < contestWorkerCount) {
      const food = active[workers.length % active.length];
      const baseSpeed = .052 + seededRandom() * .014;
      workers.push({
        foodId: food.id,
        path: food.routePath,
        index: 0,
        direction: 1,
        carrying: false,
        progress: seededRandom() * .52,
        baseSpeed,
        speed:
          baseSpeed *
          routeSpeedFactor(food.routeEfficiency || 1) *
          transportSpeedMultiplier
      });
    }
  }

  function updateContestWorkers(dt) {
    dispatchContestWorkers();
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
            contestStored += 1;
            w.carrying = false;
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

    workers = workers.filter((_,i) => !dead.has(i));
  }

  function chooseRivalFood() {
    const available = foods.filter(f => f.units > 0);
    if (!available.length) return null;

    let best = null;
    available.forEach(food => {
      const path = bfsPath(rivalNest, food);
      if (!path) return;
      const score = path.length - food.units * 1.5;
      if (!best || score < best.score) best = { food, path, score };
    });
    return best;
  }

  function dispatchRivalWorkers(now) {
    if (now < rivalStartAt) return;

    while (rivalWorkers.length < 4) {
      const target = chooseRivalFood();
      if (!target) return;

      rivalWorkers.push({
        id: `rival-${runSeed}-${Math.floor(seededRandom()*1e8)}`,
        foodId: target.food.id,
        path: target.path,
        index: 0,
        progress: seededRandom() * .28,
        speed: .043 + seededRandom() * .008,
        hp: 2,
        maxHp: 2,
        carrying: false,
        slowedUntil: 0,
        phase: 'toFood'
      });
    }
  }

  function updateRivalWorkers(now, dt) {
    dispatchRivalWorkers(now);
    const dead = new Set();

    rivalWorkers.forEach((w, idx) => {
      const slow = now < (w.slowedUntil || 0) ? .35 : 1;
      w.progress += w.speed * slow * dt;

      while (w.progress >= 1) {
        w.progress -= 1;
        w.index += 1;
        if (w.index < w.path.length - 1) continue;

        if (w.phase === 'toFood') {
          const food = foods.find(f => f.id === w.foodId);
          if (!food || food.units <= 0) {
            dead.add(idx);
            return;
          }

          food.units -= 1;
          w.carrying = true;
          w.path = w.path.slice().reverse();
          w.index = 0;
          w.progress = 0;
          w.phase = 'toNest';
          continue;
        }

        if (w.phase === 'toNest') {
          rivalStored += 1;
          w.carrying = false;

          const target = chooseRivalFood();
          if (!target) {
            dead.add(idx);
            return;
          }

          w.foodId = target.food.id;
          w.path = target.path;
          w.index = 0;
          w.progress = 0;
          w.phase = 'toFood';
        }
      }
    });

    rivalWorkers = rivalWorkers.filter((_,i) => !dead.has(i));
  }

  function updateLevelFive(now, dt) {
    if (scanMode || status !== 'playing') return;

    updateContestWorkers(dt);
    updateRivalWorkers(now, dt);

    if (contestStored >= LEVEL5_TARGET) {
      completeLevelFive(now);
      return;
    }
    if (rivalStored >= LEVEL5_TARGET) {
      failLevelFive('敌群先搬够了8份食物。');
      return;
    }

    const elapsed = now - level5StartTime;
    if (elapsed >= LEVEL5_SECONDS * 1000) {
      if (contestStored > rivalStored) completeLevelFive(now);
      else failLevelFive('时间到了，敌群的储备没有落后。');
      return;
    }

    updateUI(now);
  }

  function completeLevelFive(now = performance.now()) {
    if (status !== 'playing') return;
    status = 'won';
    const left = Math.max(0, Math.ceil(LEVEL5_SECONDS - (now - level5StartTime)/1000));
    awardLevelScore(5, 1300 + contestStored * 100 + left * 10 - rivalStored * 25);
    level6Unlocked = true;

    gameStateBadge.textContent = '第5关完成';
    gameStateBadge.style.color = '#7bf59a';
    missionTextEl.textContent =
      '资源争夺胜利。但这张二维码世界开始崩坏：最后一关，带蚁后和族群迁徙出去。';
    buffTextEl.textContent =
      `✓ 我方${contestStored} : ${rivalStored}敌方 · 当前总分${runScore}`;
    setRoadmapActive(5);
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '进入第6关：大迁徙 →';
    showToast('第5关完成！准备迁徙整个蚁群。', 3300);
  }

  function failLevelFive(reason) {
    if (status !== 'playing') return;
    status = 'lost';
    gameStateBadge.textContent = '争夺失败';
    gameStateBadge.style.color = '#ff7777';
    missionTextEl.textContent =
      `${reason} 提示：更早报信、优化路线，也可以直接咬退红色运输蚁。`;
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '重试第5关';
    showToast('食物被抢走了，再试一次！', 2600);
  }

  function drawRivalNest() {
    if (!rivalNest) return;
    const p = nodeXY(rivalNest);
    const { step } = boardMetrics();
    ctx.save();
    ctx.strokeStyle = '#ef6256';
    ctx.fillStyle = 'rgba(239,98,86,.15)';
    ctx.lineWidth = Math.max(2, step*.14);
    ctx.beginPath();
    ctx.arc(p.x,p.y,Math.max(7,step*.48),0,Math.PI*2);
    ctx.fill();
    ctx.stroke();
    ctx.restore();
  }

  function drawRivalWorkers() {
    rivalWorkers.forEach(w => {
      const p = entityPosition(w);
      const food = foods.find(f => f.id === w.foodId);
      drawAntAt(p.x,p.y,p.angle,'#ef6256',.86,w.carrying,food?.kind || 'donut');
    });
  }


  function pickMigrationExit() {
    const dist = distanceMap(nest);
    const candidates = component.filter(n => {
      const d = dist.get(nodeKey(n.r,n.c));
      const nearEdge =
        n.r <= 3 || n.c <= 3 ||
        n.r >= matrixSize - 3 || n.c >= matrixSize - 3;
      return (
        nearEdge &&
        Number.isFinite(d) &&
        d >= Math.max(14, matrixSize * .45) &&
        !isFinderForbiddenNode(n) &&
        !nodeTouchesProtected(n)
      );
    });

    if (!candidates.length) return randomPlayableNode(nest, Math.max(12,matrixSize*.4));
    candidates.sort((a,b) =>
      (dist.get(nodeKey(b.r,b.c)) || 0) - (dist.get(nodeKey(a.r,a.c)) || 0)
    );
    const top = candidates.slice(0, Math.min(12,candidates.length));
    return { ...top[Math.floor(seededRandom()*top.length)] };
  }

  function startLevelSix() {
    if (!qr || !component.length) return;

    currentLevel = 6;
    level6Unlocked = true;
    status = 'playing';
    resetStageRng(6);
    setLevelSixUI();
    gameStateBadge.textContent = '第6关 · 迁徙';
    gameStateBadge.style.color = '#d7c2ff';

    foods = [];
    workers = [];
    pheromoneRoutes = [];
    rivalWorkers = [];
    prey = [];
    enemies = [];
    mudSources = [];
    entrances = [];
    mudWorkers = [];
    flooded = new Set();

    player = { ...nest, facing:'right' };
    migrationExit = pickMigrationExit();
    migrationTrail = [{ ...nest }];
    migrationRoute = null;
    migrationExitFound = false;
    migrationQueen = null;
    migrationRaiders = [];
    migrationFlooded = new Set();
    migrationFloodFrontier = [];
    migrationFloodStarted = false;
    migrationFloodAt = 0;
    lastMigrationFloodTick = 0;
    migrationEfficiency = 1;
    level6StartTime = performance.now();
    lastAcidTime = 0;
    acidEffectUntil = 0;
    scanPauseStarted = 0;

    missionTextEl.textContent =
      '从绿色旧巢出发，先找到蓝色迁徙出口。你走出去的路线，就是蚁后稍后要走的路线。';
    updateUI(level6StartTime);
    showToast(`最终关：${LEVEL6_SCOUT_SECONDS}秒内找到迁徙出口并回巢！`, 3000);
    requestRender();
  }

  function handleLevelSixPlayerMove() {
    if (!migrationExitFound) {
      const last = migrationTrail[migrationTrail.length-1];
      if (!last || !sameNode(last,player)) migrationTrail.push({r:player.r,c:player.c});

      if (sameNode(player,migrationExit)) {
        migrationExitFound = true;
        migrationRoute = migrationTrail.slice();
        if (!sameNode(migrationRoute[0],nest)) migrationRoute.unshift({...nest});
        if (!sameNode(migrationRoute[migrationRoute.length-1],migrationExit)) {
          migrationRoute.push({...migrationExit});
        }
        migrationEfficiency = routeEfficiency(migrationRoute,nest,migrationExit);
        missionTextEl.textContent =
          `出口找到了！迁徙路线效率${Math.round(migrationEfficiency*100)}%。现在回绿色旧巢，把蚁后带出来。`;
        showToast('找到迁徙出口！快回巢带蚁后出发。',2200);
      }
      return;
    }

    if (!migrationQueen && sameNode(player,nest)) {
      beginMigrationEscort();
    }
  }

  function beginMigrationEscort() {
    if (migrationQueen || !migrationRoute?.length) return;

    migrationQueen = {
      path:migrationRoute,
      index:0,
      progress:0,
      speed:.034 * routeSpeedFactor(migrationEfficiency) * Math.min(1.12,transportSpeedMultiplier),
      hp:5,
      maxHp:5
    };

    migrationFloodAt = performance.now() + 6000;
    spawnMigrationRaiders();
    missionTextEl.textContent =
      '蚁后出发了！洪水6秒后从旧巢追来。沿迁徙路线护送，优先清掉挡路的红色敌蚁。';
    showToast('👑 蚁后开始迁徙！6秒后洪水追来！',2400);
  }

  function spawnMigrationRaiders() {
    migrationRaiders = [];
    if (!migrationRoute || migrationRoute.length < 8) return;

    [0.34,0.58,0.80].forEach((ratio,i) => {
      const targetIndex = Math.min(
        migrationRoute.length-2,
        Math.max(2,Math.floor(migrationRoute.length*ratio))
      );
      const target = migrationRoute[targetIndex];
      let start = randomPlayableNode(target,Math.max(8,matrixSize*.22));
      let path = bfsPath(start,target);

      for (let tries=0;(!path || path.length<4) && tries<8;tries++) {
        start = randomPlayableNode(target,Math.max(6,matrixSize*.18));
        path = bfsPath(start,target);
      }
      if (!path || path.length<2) return;

      migrationRaiders.push({
        id:`raider-${runSeed}-${i}`,
        path,
        index:0,
        progress:seededRandom()*.25,
        speed:(i===2?.030:.036)+seededRandom()*.005,
        hp:i===2?4:2,
        maxHp:i===2?4:2,
        big:i===2,
        slowedUntil:0,
        arrived:false,
        targetNode:{...target},
        targetIndex
      });
    });
  }

  function updateMigrationRaiders(now,dt) {
    migrationRaiders.forEach(r => {
      if (r.arrived) return;
      const slow = now < (r.slowedUntil||0) ? .35 : 1;
      r.progress += r.speed * slow * dt;

      while (r.progress>=1) {
        r.progress-=1;
        r.index+=1;
        if (r.index>=r.path.length-1) {
          r.index=r.path.length-1;
          r.progress=0;
          r.arrived=true;
          r.node={...r.targetNode};
          break;
        }
      }
    });
  }

  function migrationQueenNode() {
    if (!migrationQueen) return nest;
    return migrationQueen.path[
      Math.max(0,Math.min(migrationQueen.path.length-1,migrationQueen.index))
    ];
  }

  function migrationPathBlocked() {
    if (!migrationQueen) return false;
    const nextIndex = Math.min(migrationQueen.path.length-1,migrationQueen.index+1);
    const next = migrationQueen.path[nextIndex];

    return migrationRaiders.some(r => {
      if (!r.arrived) return false;
      const n = r.targetNode || r.node;
      return Math.hypot(n.r-next.r,n.c-next.c)<=1.25;
    });
  }

  function updateMigrationQueen(dt) {
    if (!migrationQueen || migrationPathBlocked()) return;

    migrationQueen.progress += migrationQueen.speed * dt;
    while (migrationQueen.progress>=1) {
      migrationQueen.progress-=1;
      migrationQueen.index+=1;

      if (migrationQueen.index>=migrationQueen.path.length-1) {
        migrationQueen.index=migrationQueen.path.length-1;
        migrationQueen.progress=0;
        completeLevelSix();
        return;
      }
    }
  }

  function startMigrationFlood(now) {
    if (migrationFloodStarted) return;
    migrationFloodStarted=true;
    lastMigrationFloodTick=now;
    const k=nodeKey(nest.r,nest.c);
    migrationFlooded.add(k);
    migrationFloodFrontier=[{...nest}];
    gameStateBadge.textContent='洪水追来了';
    gameStateBadge.style.color='#5dc8ff';
    showToast('🌊 洪水从旧巢涌来了！别让它追上蚁后。',2000);
  }

  function updateMigrationFlood(now) {
    if (!migrationQueen) return;
    if (!migrationFloodStarted) {
      if (now>=migrationFloodAt) startMigrationFlood(now);
      else return;
    }

    if (now-lastMigrationFloodTick<MIGRATION_FLOOD_INTERVAL) return;
    lastMigrationFloodTick=now;

    const nextFrontier=[];
    let budget=1;
    while (migrationFloodFrontier.length && budget>0) {
      const cur=migrationFloodFrontier.shift();
      for (const n of graph.get(nodeKey(cur.r,cur.c))||[]) {
        const k=nodeKey(n.r,n.c);
        if (!componentSet.has(k)||migrationFlooded.has(k)) continue;
        migrationFlooded.add(k);
        nextFrontier.push({...n});
        budget-=1;
        if (budget<=0) break;
      }
    }
    migrationFloodFrontier.push(...nextFrontier);

    const q=migrationQueenNode();
    if (migrationFlooded.has(nodeKey(q.r,q.c))) {
      failLevelSix('洪水追上了蚁后。');
    }
  }

  function updateLevelSix(now,dt) {
    if (scanMode || status!=='playing') return;

    if (!migrationQueen) {
      const elapsed=now-level6StartTime;
      if (elapsed>=LEVEL6_SCOUT_SECONDS*1000) {
        failLevelSix(
          migrationExitFound
            ? '找到出口后没能及时回巢。'
            : '侦察时间结束，还没有找到迁徙出口。'
        );
        return;
      }
      updateUI(now);
      return;
    }

    updateMigrationRaiders(now,dt);
    updateMigrationQueen(dt);
    if (status!=='playing') return;
    updateMigrationFlood(now);
    if (status!=='playing') return;
    updateUI(now);
  }

  function completeLevelSix() {
    if (status!=='playing') return;
    status='won';
    const elapsed=(performance.now()-level6StartTime)/1000;
    awardLevelScore(
      6,
      2200 + migrationEfficiency*1100 + Math.max(0,120-elapsed)*8 + migrationQueen.hp*80
    );

    gameStateBadge.textContent='迁徙成功';
    gameStateBadge.style.color='#7bf59a';
    missionTextEl.textContent =
      '蚁后和族群已经离开这张二维码。这个世界成为了你的蚁群历史，也可以变成朋友的同图挑战。';
    buffTextEl.textContent=`最终总分 ${runScore} · ${runGrade()}级`;
    setRoadmapActive(6);
    nextLevelBtn.hidden=true;
    showToast('大迁徙成功！这一代蚁群活下来了 👑',3600);
    setTimeout(showFinalResult,650);
  }

  function failLevelSix(reason) {
    if (status!=='playing') return;
    status='lost';
    gameStateBadge.textContent='迁徙失败';
    gameStateBadge.style.color='#ff7777';
    missionTextEl.textContent =
      `${reason} 最终关考验的是探路效率、清路和护送，不只是跑得快。`;
    nextLevelBtn.hidden=false;
    nextLevelBtn.disabled=false;
    nextLevelBtn.textContent='重试第6关';
    showToast('迁徙失败，再给蚁群一次机会。',2800);
  }

  function drawMigrationExit() {
    if (!migrationExit) return;
    const p=nodeXY(migrationExit);
    const {step}=boardMetrics();
    ctx.save();
    ctx.strokeStyle='#6fd9ff';
    ctx.fillStyle='rgba(111,217,255,.13)';
    ctx.lineWidth=Math.max(2,step*.12);
    ctx.setLineDash([Math.max(3,step*.18),Math.max(2,step*.12)]);
    ctx.beginPath();
    ctx.arc(p.x,p.y,Math.max(9,step*.62),0,Math.PI*2);
    ctx.fill();
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle='#dff7ff';
    ctx.font=`900 ${Math.max(9,step*.34)}px system-ui`;
    ctx.textAlign='center';
    ctx.textBaseline='middle';
    ctx.fillText('EXIT',p.x,p.y+.5);
    ctx.restore();
  }

  function drawMigrationRoute() {
    if (!migrationRoute) return;
    const {step}=boardMetrics();
    ctx.save();
    ctx.fillStyle='rgba(202,172,255,.46)';
    migrationRoute.forEach((node,i)=>{
      if (i%2) return;
      const p=nodeXY(node);
      ctx.beginPath();
      ctx.arc(p.x,p.y,Math.max(1.5,step*.09),0,Math.PI*2);
      ctx.fill();
    });
    ctx.restore();
  }

  function drawMigrationQueen() {
    if (!migrationQueen) return;
    const p=entityPosition(migrationQueen);
    drawAntAt(p.x,p.y,p.angle,'#c9a4ff',1.42,false);

    const {step}=boardMetrics();
    ctx.save();
    ctx.fillStyle='#ffe58a';
    ctx.font=`${Math.max(10,step*.52)}px serif`;
    ctx.textAlign='center';
    ctx.textBaseline='middle';
    ctx.fillText('♛',p.x,p.y-step*.62);
    ctx.restore();
  }

  function drawMigrationRaiders() {
    migrationRaiders.forEach(r=>{
      const p=entityPosition(r);
      const slowed=performance.now()<(r.slowedUntil||0);
      drawAntAt(
        p.x,p.y,p.angle,
        slowed?'#8b8fcf':(r.big?'#c43b33':'#ef6256'),
        r.big?1.18:.92,
        false
      );
    });
  }

  function drawMigrationFlood() {
    const {step}=boardMetrics();
    ctx.save();
    ctx.fillStyle='rgba(49,174,255,.48)';
    migrationFlooded.forEach(k=>{
      const p=nodeXY(parseKey(k));
      ctx.beginPath();
      ctx.arc(p.x,p.y,Math.max(2.2,step*.18),0,Math.PI*2);
      ctx.fill();
    });
    ctx.restore();
  }

  function updateEnemies(dt) {
    if (scanMode || currentLevel !== 3 || status !== 'playing') return;
    const escaped = new Set();

    enemies.forEach((enemy, idx) => {
      enemy.progress += enemy.speed * dt;
      while (enemy.progress >= 1) {
        enemy.progress -= 1;
        enemy.index += 1;

        if (enemy.index >= enemy.path.length - 1) {
          nestHp = Math.max(0, nestHp - (enemy.big ? 2 : 1));
          escaped.add(idx);
          showToast(enemy.big ? '大型敌蚁冲进蚁穴！生命 -2' : '敌蚁冲进蚁穴！生命 -1', 1400);
          if (nestHp <= 0) {
            failLevelThree();
            return;
          }
          break;
        }
      }
    });

    enemies = enemies.filter((_, i) => !escaped.has(i));
  }

  function combatTargetsForLevel() {
    if (currentLevel === 3) return enemies;
    if (currentLevel === 4) return prey;
    if (currentLevel === 5) return rivalWorkers;
    if (currentLevel === 6) return migrationRaiders;
    return [];
  }

  function defeatCombatTarget(target) {
    if (currentLevel === 3) {
      enemies = enemies.filter(e => e !== target);
      enemiesDefeated += 1;
      showToast(target.big ? '击退大型敌蚁！' : '击退敌蚁！', 950);
      return;
    }

    if (currentLevel === 4) {
      prey = prey.filter(e => e !== target);
      preyDefeated += 1;
      showToast(target.big ? '猎倒大型甲虫！' : '猎倒甲虫！', 900);
      return;
    }

    if (currentLevel === 5) {
      if (target.carrying && target.foodId) {
        const food = foods.find(f => f.id === target.foodId);
        if (food) food.units += 1;
      }
      rivalWorkers = rivalWorkers.filter(e => e !== target);
      showToast('赶跑一只抢食物的敌蚁！', 850);
      return;
    }

    if (currentLevel === 6) {
      migrationRaiders = migrationRaiders.filter(e => e !== target);
      showToast('清掉一只拦路敌蚁！', 850);
    }
  }

  function biteAttack() {
    if (currentLevel < 3 || currentLevel > 6 || status !== 'playing' || scanMode) {
      if (currentLevel < 3) showToast('🦷 咬击会在第3关「入侵者」解锁。', 1400);
      return;
    }

    const now = performance.now();
    if (now - lastBiteTime < BITE_COOLDOWN) return;
    lastBiteTime = now;
    biteEffectUntil = now + 120;

    const pp = nodeXY(player);
    const facing = {
      right: [1, 0],
      left: [-1, 0],
      down: [0, 1],
      up: [0, -1]
    }[player.facing] || [1, 0];
    const { step } = boardMetrics();
    const range = Math.max(24, step * 2.05);

    let best = null;
    combatTargetsForLevel().forEach(target => {
      const ep = entityPosition(target);
      const dx = ep.x - pp.x;
      const dy = ep.y - pp.y;
      const d = Math.hypot(dx, dy);
      if (d > range) return;
      const dot = d < .01 ? 1 : (dx / d) * facing[0] + (dy / d) * facing[1];
      if (dot < .18) return;
      if (!best || d < best.d) best = { target, d };
    });

    if (!best) {
      showToast('咬空了', 550);
      requestRender();
      return;
    }

    const biteDamage = 1 + biteDamageBonus;
    best.target.hp -= biteDamage;
    if (best.target.hp <= 0) {
      defeatCombatTarget(best.target);
    } else {
      showToast(`咬中！伤害 ${biteDamage} · 目标还剩 ${best.target.hp}`, 700);
    }
    requestRender();
  }

  function guardNodes() {
    if (!guardCount) return [];
    const seen = new Set([nodeKey(nest.r, nest.c)]);
    const queue = [{ ...nest }];
    const result = [];

    while (queue.length && result.length < guardCount) {
      const cur = queue.shift();
      for (const n of graph.get(nodeKey(cur.r, cur.c)) || []) {
        const k = nodeKey(n.r, n.c);
        if (seen.has(k) || !componentSet.has(k) || isFinderForbiddenNode(n)) continue;
        seen.add(k);
        queue.push(n);
        result.push(n);
        if (result.length >= guardCount) break;
      }
    }
    return result;
  }

  function updateGuards(now) {
    if (!guardCount || !enemies.length || currentLevel !== 3 || status !== 'playing') return;
    const cooldown = Math.max(300, GUARD_BASE_COOLDOWN / guardCount);
    if (now - lastGuardAttack < cooldown) return;

    const { step } = boardMetrics();
    const nestPos = nodeXY(nest);
    const range = Math.max(42, step * 4.2);
    let best = null;

    enemies.forEach(enemy => {
      const p = enemyPosition(enemy);
      const d = Math.hypot(p.x - nestPos.x, p.y - nestPos.y);
      if (d <= range && (!best || d < best.d)) best = { enemy, d };
    });

    if (!best) return;
    lastGuardAttack = now;
    guardFlashUntil = now + 140;
    best.enemy.hp -= 1;

    if (best.enemy.hp <= 0) {
      enemies = enemies.filter(e => e !== best.enemy);
      enemiesDefeated += 1;
      showToast('守卫蚁击退了一只入侵者！', 900);
    }
  }

  function drawGuards() {
    if (!guardCount) return;
    const nodes = guardNodes();
    const nestPos = nodeXY(nest);

    nodes.forEach((node, i) => {
      const p = nodeXY(node);
      const angle = Math.atan2(nestPos.y - p.y, nestPos.x - p.x);
      drawAntAt(
        p.x,
        p.y,
        angle,
        performance.now() < guardFlashUntil ? '#9df7b7' : '#63d99a',
        .78 + Math.min(.08, i * .02),
        false
      );
    });
  }

  function updateLevelThree(now, dt) {
    if (scanMode || status !== 'playing') return;

    const elapsed = now - level3StartTime;
    const spawnInterval = Math.max(1800, 3400 - Math.floor(elapsed / 12000) * 350);
    if (!lastEnemySpawn || now - lastEnemySpawn >= spawnInterval) {
      spawnEnemy();
      lastEnemySpawn = now;
    }

    updateGuards(now);
    updateEnemies(dt);
    if (status !== 'playing') return;

    if (elapsed >= LEVEL3_SECONDS * 1000) {
      completeLevelThree();
      return;
    }
    updateUI(now);
  }

  function completeLevelThree() {
    if (status !== 'playing') return;
    status = 'won';
    enemies = [];
    awardLevelScore(
      3,
      1100 + nestHp * 110 + enemiesDefeated * 28
    );
    level4Unlocked = true;
    gameStateBadge.textContent = '第3关完成';
    gameStateBadge.style.color = '#7bf59a';
    missionTextEl.textContent =
      '敌蚁退去了。下一关解锁F蚁酸：主动追猎会逃跑的甲虫。';
    buffTextEl.textContent =
      `✓ 击退 ${enemiesDefeated}只敌蚁 · 当前总分 ${runScore}`;
    populationBarEl.style.width =
      `${Math.max(0,(nestHp/level3MaxNestHp())*100)}%`;
    setRoadmapActive(3);
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '进入第4关：狩猎 →';
    showToast('第3关完成！F 蚁酸即将解锁 💧', 3200);
  }

  function failLevelThree() {
    if (status !== 'playing') return;
    status = 'lost';
    gameStateBadge.textContent = '蚁穴失守';
    gameStateBadge.style.color = '#ff7777';
    missionTextEl.textContent = '敌蚁冲进了蚁穴。不要追着敌人跑，优先站在通向蚁穴的岔路口拦截。';
    buffTextEl.textContent = '失败提示：咬击只攻击你面前的近距离敌人';
    nextLevelBtn.hidden = false;
    nextLevelBtn.disabled = false;
    nextLevelBtn.textContent = '重试第3关';
    showToast('蚁穴失守，再试一次！', 3200);
  }

  function drawEnemies() {
    enemies.forEach(enemy => {
      const p = enemyPosition(enemy);
      drawAntAt(p.x, p.y, p.angle, enemy.big ? '#d43d32' : '#ef6256', enemy.big ? 1.22 : .92, false);

      if (enemy.big || enemy.hp < enemy.maxHp) {
        const { step } = boardMetrics();
        const w = Math.max(14, step * .9);
        const h = Math.max(2, step * .09);
        ctx.save();
        ctx.fillStyle = 'rgba(45,16,12,.72)';
        ctx.fillRect(p.x - w/2, p.y - step * .62, w, h);
        ctx.fillStyle = '#ff6d61';
        ctx.fillRect(p.x - w/2, p.y - step * .62, w * (enemy.hp / enemy.maxHp), h);
        ctx.restore();
      }
    });
  }

  function drawBiteEffect() {
    if (currentLevel < 3 || currentLevel > 6 || performance.now() > biteEffectUntil) return;
    const p = nodeXY(player);
    const { step } = boardMetrics();
    const offset = step * .72;
    const pos = {
      right: [offset, 0],
      left: [-offset, 0],
      down: [0, offset],
      up: [0, -offset]
    }[player.facing] || [offset, 0];

    ctx.save();
    ctx.strokeStyle = 'rgba(255, 210, 90, .95)';
    ctx.lineWidth = Math.max(2, step * .11);
    ctx.beginPath();
    ctx.arc(p.x + pos[0], p.y + pos[1], Math.max(8, step * .48), -.7, .7);
    ctx.stroke();
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
    pheromoneRoutes.forEach(route => {
      const efficiency = route.efficiency || 1;
      ctx.fillStyle =
        efficiency >= .85
          ? 'rgba(91, 214, 115, .48)'
          : efficiency >= .65
            ? 'rgba(239, 178, 68, .48)'
            : 'rgba(232, 100, 76, .48)';

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

    if (currentLevel === 2 && reportedMudSource) {
      const { step } = boardMetrics();
      const n = nodeXY(nest);
      ctx.save();
      ctx.strokeStyle = '#c98243';
      ctx.lineWidth = Math.max(1, step * .08);
      ctx.setLineDash([Math.max(2, step * .15), Math.max(2, step * .15)]);
      ctx.beginPath();
      ctx.moveTo(p.x, p.y);
      ctx.lineTo(n.x, n.y);
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
    } else if (currentLevel === 3) {
      drawNest();
      drawGuards();
      drawEnemies();
      drawPlayer();
      drawBiteEffect();
    } else if (currentLevel === 4) {
      drawNest();
      drawPrey();
      drawPlayer();
      drawBiteEffect();
      drawAcidEffect();
    } else if (currentLevel === 5) {
      drawPheromones();
      foods.forEach(drawFood);
      drawNest();
      drawRivalNest();
      drawWorkers();
      drawRivalWorkers();
      drawPlayer();
      drawBiteEffect();
      drawAcidEffect();
    } else if (currentLevel === 6) {
      drawMigrationFlood();
      drawMigrationRoute();
      drawMigrationExit();
      drawNest();
      drawMigrationQueen();
      drawMigrationRaiders();
      drawPlayer();
      drawBiteEffect();
      drawAcidEffect();
    } else {
      drawPheromones();
      foods.forEach(drawFood);
      drawNest();
      drawWorkers();
      drawPlayer();
    }

    drawQRProtection();
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
      else if (currentLevel === 3) updateLevelThree(now, dt);
      else if (currentLevel === 4) updateLevelFour(now, dt);
      else if (currentLevel === 5) updateLevelFive(now, dt);
      else if (currentLevel === 6) updateLevelSix(now, dt);
      else {
        updateWorkers(dt);
        updateUI(now);
      }
    }

    requestRender();
    maybeVerifyGameplayQR(now);
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
      biteAttack();
    } else if (e.code === 'KeyF') {
      e.preventDefault();
      acidAttack();
    }
  }

  document.addEventListener('keydown', handleKey, { passive: false });

  nextLevelBtn.addEventListener('click', () => {
    if (currentLevel === 1 && level2Unlocked) startLevelTwo();
    else if (currentLevel === 2 && status === 'lost') startLevelTwo();
    else if (currentLevel === 2 && status === 'won' && level3Unlocked) startLevelThree();
    else if (currentLevel === 3 && status === 'lost') startLevelThree();
    else if (currentLevel === 3 && status === 'won' && level4Unlocked) startLevelFour();
    else if (currentLevel === 4 && status === 'lost') startLevelFour();
    else if (currentLevel === 4 && status === 'won' && level5Unlocked) startLevelFive();
    else if (currentLevel === 5 && status === 'lost') startLevelFive();
    else if (currentLevel === 5 && status === 'won' && level6Unlocked) startLevelSix();
    else if (currentLevel === 6 && status === 'lost') startLevelSix();
  });

  roadmap2El.addEventListener('click', () => {
    if (level2Unlocked && currentLevel !== 2) startLevelTwo();
  });

  roadmap3El.addEventListener('click', () => {
    if (level3Unlocked && currentLevel !== 3) startLevelThree();
  });

  roadmap4El.addEventListener('click', () => {
    if (level4Unlocked && currentLevel !== 4) startLevelFour();
  });

  roadmap5El.addEventListener('click', () => {
    if (level5Unlocked && currentLevel !== 5) startLevelFive();
  });

  roadmap6El.addEventListener('click', () => {
    if (level6Unlocked && currentLevel !== 6) startLevelSix();
  });

  biteBtn.addEventListener('click', biteAttack);
  if (mobileBiteBtn) mobileBiteBtn.addEventListener('click', biteAttack);
  acidBtn.addEventListener('click', acidAttack);
  if (mobileAcidBtn) mobileAcidBtn.addEventListener('click', acidAttack);

  shareBtn.addEventListener('click', () => shareChallenge(false));
  shareRunBtn.addEventListener('click', () => shareChallenge(true));

  replayChallengeBtn.addEventListener('click', () => {
    resultOverlayEl.hidden = true;
    resetGame(qrPayload, runSeed, true);
  });

  newWorldBtn.addEventListener('click', () => {
    resultOverlayEl.hidden = true;
    resetGame(qrInput.value.trim() || qrPayload || 'QR Ant Colony', freshSeed(), true);
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
    resetGame(qrInput.value.trim() || 'QR Ant Colony', freshSeed(), true);
  });

  qrInput.addEventListener('keydown', e => {
    if (e.key === 'Enter') resetGame(qrInput.value.trim() || 'QR Ant Colony', freshSeed(), true);
  });

  scanBtn.addEventListener('click', () => {
    const now = performance.now();
    if (!scanMode && currentLevel >= 2 && currentLevel <= 6 && status === 'playing') {
      scanPauseStarted = now;
    } else if (scanMode && status === 'playing' && scanPauseStarted) {
      const pausedFor = now - scanPauseStarted;
      if (currentLevel === 2) level2StartTime += pausedFor;
      if (currentLevel === 3) level3StartTime += pausedFor;
      if (currentLevel === 4) level4StartTime += pausedFor;
      if (currentLevel === 5) {
        level5StartTime += pausedFor;
        rivalStartAt += pausedFor;
      }
      if (currentLevel === 6) {
        level6StartTime += pausedFor;
        if (migrationFloodAt) migrationFloodAt += pausedFor;
      }
      scanPauseStarted = 0;
    }

    scanMode = !scanMode;
    if (scanMode) setScanHealth('good', '✓ 纯黑白扫码模式');
    else {
      lastQrVerifyAt = 0;
      setScanHealth('checking', '正在重新检测游戏画面...');
    }
    scanBtn.textContent = scanMode ? '返回游戏' : '扫码模式';
    showToast(scanMode ? '已隐藏游戏元素，可直接扫码；限时关卡计时暂停。' : '继续探索蚁穴。');
    requestRender();
  });

  const initialParams = new URLSearchParams(location.search);
  const sharedContent = initialParams.get('q');
  const sharedSeedRaw = initialParams.get('s');
  const sharedSeed = sharedSeedRaw ? parseInt(sharedSeedRaw, 36) : NaN;

  if (sharedContent) {
    qrInput.value = sharedContent;
    resetGame(sharedContent, Number.isFinite(sharedSeed) ? sharedSeed : hashSeed(sharedContent), false);
    showToast('好友挑战已载入：同一二维码、同一世界种子。', 3000);
  } else {
    resetGame(qrInput.value, freshSeed(), true);
  }
  requestAnimationFrame(loop);
})();