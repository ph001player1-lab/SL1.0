/* qr.js — компактный QR-энкодер. Byte mode, уровень коррекции M, версии 1–6.
   Зависимостей нет: работает офлайн, после первой загрузки страницы сеть не нужна.
   API:  QR.matrix(text) -> [[0|1,...],...]   QR.svg(text, opts) -> строка SVG   */
(function (global) {
  'use strict';

  // [всего кодовых слов, EC на блок, [[блоков, данных в блоке], ...]]
  var SPEC = {
    1: { total: 26,  ec: 10, groups: [[1, 16]] },
    2: { total: 44,  ec: 16, groups: [[1, 28]] },
    3: { total: 70,  ec: 26, groups: [[1, 44]] },
    4: { total: 100, ec: 18, groups: [[2, 32]] },
    5: { total: 134, ec: 24, groups: [[2, 43]] },
    6: { total: 172, ec: 16, groups: [[4, 27]] }
  };
  var ALIGN = { 1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30], 6: [6, 34] };

  // ---- поле Галуа GF(256), примитивный полином 0x11D ----
  var EXP = new Uint8Array(512), LOG = new Uint8Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) {
      EXP[i] = x; LOG[x] = i;
      x <<= 1; if (x & 0x100) x ^= 0x11d;
    }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();
  function gmul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function rsGenerator(deg) {
    var poly = [1];
    for (var i = 0; i < deg; i++) {
      var next = new Array(poly.length + 1).fill(0);
      for (var j = 0; j < poly.length; j++) {
        next[j] ^= gmul(poly[j], 1);
        next[j + 1] ^= gmul(poly[j], EXP[i]);
      }
      poly = next;
    }
    return poly;
  }

  function rsEncode(data, ecLen) {
    var gen = rsGenerator(ecLen);
    var res = new Array(ecLen).fill(0);
    for (var i = 0; i < data.length; i++) {
      var factor = data[i] ^ res[0];
      res.shift(); res.push(0);
      for (var j = 0; j < ecLen; j++) res[j] ^= gmul(gen[j + 1], factor);
    }
    return res;
  }

  function utf8Bytes(str) {
    var out = [], i, c;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) { out.push(0xc0 | (c >> 6), 0x80 | (c & 63)); }
      else if (c >= 0xd800 && c <= 0xdbff && i + 1 < str.length) {
        var c2 = str.charCodeAt(++i);
        var cp = 0x10000 + ((c - 0xd800) << 10) + (c2 - 0xdc00);
        out.push(0xf0 | (cp >> 18), 0x80 | ((cp >> 12) & 63), 0x80 | ((cp >> 6) & 63), 0x80 | (cp & 63));
      } else { out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63)); }
    }
    return out;
  }

  function pickVersion(len) {
    for (var v = 1; v <= 6; v++) {
      var s = SPEC[v], dataWords = 0;
      s.groups.forEach(function (g) { dataWords += g[0] * g[1]; });
      if (4 + 8 + 8 * len <= dataWords * 8) return v;
    }
    throw new Error('QR: слишком длинная строка (максимум 106 байт)');
  }

  function buildCodewords(bytes, version) {
    var s = SPEC[version], dataWords = 0;
    s.groups.forEach(function (g) { dataWords += g[0] * g[1]; });

    var bits = [];
    function push(val, n) { for (var i = n - 1; i >= 0; i--) bits.push((val >> i) & 1); }
    push(0x4, 4);            // режим: байты
    push(bytes.length, 8);   // счётчик (версии 1–9)
    bytes.forEach(function (b) { push(b, 8); });

    var cap = dataWords * 8;
    for (var t = 0; t < 4 && bits.length < cap; t++) bits.push(0);  // терминатор
    while (bits.length % 8) bits.push(0);

    var words = [];
    for (var i = 0; i < bits.length; i += 8) {
      var b = 0; for (var k = 0; k < 8; k++) b = (b << 1) | bits[i + k];
      words.push(b);
    }
    var pad = [0xec, 0x11], p = 0;
    while (words.length < dataWords) words.push(pad[p++ % 2]);

    // разбивка на блоки
    var blocks = [], ecBlocks = [], pos = 0;
    s.groups.forEach(function (g) {
      for (var b = 0; b < g[0]; b++) {
        var chunk = words.slice(pos, pos + g[1]); pos += g[1];
        blocks.push(chunk);
        ecBlocks.push(rsEncode(chunk, s.ec));
      }
    });

    // чередование
    var out = [], maxData = Math.max.apply(null, blocks.map(function (b) { return b.length; }));
    for (var c = 0; c < maxData; c++)
      for (var bi = 0; bi < blocks.length; bi++)
        if (c < blocks[bi].length) out.push(blocks[bi][c]);
    for (var e = 0; e < s.ec; e++)
      for (var bj = 0; bj < ecBlocks.length; bj++) out.push(ecBlocks[bj][e]);
    return out;
  }

  function placeFunction(m, res, version) {
    var size = m.length;
    function finder(r, c) {
      for (var i = -1; i <= 7; i++) for (var j = -1; j <= 7; j++) {
        var rr = r + i, cc = c + j;
        if (rr < 0 || cc < 0 || rr >= size || cc >= size) continue;
        var on = (i >= 0 && i <= 6 && (j === 0 || j === 6)) ||
                 (j >= 0 && j <= 6 && (i === 0 || i === 6)) ||
                 (i >= 2 && i <= 4 && j >= 2 && j <= 4);
        m[rr][cc] = on ? 1 : 0; res[rr][cc] = 1;
      }
    }
    finder(0, 0); finder(0, size - 7); finder(size - 7, 0);

    for (var i = 8; i < size - 8; i++) {
      var v = (i % 2 === 0) ? 1 : 0;
      m[6][i] = v; res[6][i] = 1;
      m[i][6] = v; res[i][6] = 1;
    }

    var ap = ALIGN[version];
    for (var a = 0; a < ap.length; a++) for (var b = 0; b < ap.length; b++) {
      var r = ap[a], c = ap[b];
      if (res[r][c]) continue;
      for (var dy = -2; dy <= 2; dy++) for (var dx = -2; dx <= 2; dx++) {
        var on2 = Math.max(Math.abs(dy), Math.abs(dx)) !== 1;
        m[r + dy][c + dx] = on2 ? 1 : 0; res[r + dy][c + dx] = 1;
      }
    }

    for (var k = 0; k < 9; k++) {
      if (!res[8][k]) { res[8][k] = 1; m[8][k] = 0; }
      if (!res[k][8]) { res[k][8] = 1; m[k][8] = 0; }
    }
    for (var t = 0; t < 8; t++) {
      res[8][size - 1 - t] = 1; m[8][size - 1 - t] = 0;
      res[size - 1 - t][8] = 1; m[size - 1 - t][8] = 0;
    }
    m[size - 8][8] = 1; res[size - 8][8] = 1;   // тёмный модуль
  }

  function placeData(m, res, codewords) {
    var size = m.length, bitIdx = 0, upward = true;
    function bit() {
      if (bitIdx >= codewords.length * 8) return 0;
      var b = (codewords[bitIdx >> 3] >> (7 - (bitIdx & 7))) & 1;
      bitIdx++; return b;
    }
    for (var right = size - 1; right > 0; right -= 2) {
      if (right === 6) right = 5;
      for (var vert = 0; vert < size; vert++) {
        var row = upward ? size - 1 - vert : vert;
        for (var col = 0; col < 2; col++) {
          var c = right - col;
          if (res[row][c]) continue;
          m[row][c] = bit();
        }
      }
      upward = !upward;
    }
  }

  var MASKS = [
    function (i, j) { return (i + j) % 2 === 0; },
    function (i) { return i % 2 === 0; },
    function (i, j) { return j % 3 === 0; },
    function (i, j) { return (i + j) % 3 === 0; },
    function (i, j) { return (Math.floor(i / 2) + Math.floor(j / 3)) % 2 === 0; },
    function (i, j) { return ((i * j) % 2) + ((i * j) % 3) === 0; },
    function (i, j) { return (((i * j) % 2) + ((i * j) % 3)) % 2 === 0; },
    function (i, j) { return (((i + j) % 2) + ((i * j) % 3)) % 2 === 0; }
  ];

  function penalty(m) {
    var size = m.length, score = 0, i, j, run, dark = 0;
    for (i = 0; i < size; i++) {
      run = 1;
      for (j = 1; j < size; j++) {
        if (m[i][j] === m[i][j - 1]) { run++; if (run === 5) score += 3; else if (run > 5) score += 1; }
        else run = 1;
      }
      run = 1;
      for (j = 1; j < size; j++) {
        if (m[j][i] === m[j - 1][i]) { run++; if (run === 5) score += 3; else if (run > 5) score += 1; }
        else run = 1;
      }
    }
    for (i = 0; i < size - 1; i++) for (j = 0; j < size - 1; j++) {
      var s = m[i][j] + m[i][j + 1] + m[i + 1][j] + m[i + 1][j + 1];
      if (s === 0 || s === 4) score += 3;
    }
    var pat1 = [1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0], pat2 = [0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1];
    function scan(get) {
      for (i = 0; i < size; i++) for (j = 0; j + 11 <= size; j++) {
        var ok1 = true, ok2 = true;
        for (var k = 0; k < 11; k++) {
          var v = get(i, j + k);
          if (v !== pat1[k]) ok1 = false;
          if (v !== pat2[k]) ok2 = false;
        }
        if (ok1) score += 40;
        if (ok2) score += 40;
      }
    }
    scan(function (a, b) { return m[a][b]; });
    scan(function (a, b) { return m[b][a]; });
    for (i = 0; i < size; i++) for (j = 0; j < size; j++) dark += m[i][j];
    score += Math.floor(Math.abs(dark * 100 / (size * size) - 50) / 5) * 10;
    return score;
  }

  function formatBits(mask) {
    var data = (0x00 << 3) | mask;          // уровень M = 00
    var rem = data << 10;
    for (var i = 14; i >= 10; i--) if ((rem >> i) & 1) rem ^= 0x537 << (i - 10);
    return ((data << 10) | rem) ^ 0x5412;
  }

  function placeFormat(m, mask) {
    var size = m.length, bits = formatBits(mask), str = [], p;
    for (var i = 14; i >= 0; i--) str.push((bits >> i) & 1);   // str[0] = старший бит

    var copy1 = [[8, 0], [8, 1], [8, 2], [8, 3], [8, 4], [8, 5], [8, 7], [8, 8],
                 [7, 8], [5, 8], [4, 8], [3, 8], [2, 8], [1, 8], [0, 8]];
    var copy2 = [];
    for (var k = 0; k <= 6; k++) copy2.push([size - 1 - k, 8]);
    for (var t = 0; t <= 7; t++) copy2.push([8, size - 8 + t]);

    for (p = 0; p < 15; p++) {
      m[copy1[p][0]][copy1[p][1]] = str[p];
      m[copy2[p][0]][copy2[p][1]] = str[p];
    }
    m[size - 8][8] = 1;   // тёмный модуль поверх
  }

  function matrix(text) {
    var bytes = utf8Bytes(String(text));
    var version = pickVersion(bytes.length);
    var size = 17 + 4 * version;

    var base = [], res = [];
    for (var i = 0; i < size; i++) { base.push(new Array(size).fill(0)); res.push(new Array(size).fill(0)); }
    placeFunction(base, res, version);
    placeData(base, res, buildCodewords(bytes, version));

    var best = null, bestScore = Infinity;
    for (var mk = 0; mk < 8; mk++) {
      var cand = base.map(function (r) { return r.slice(); });
      for (var r2 = 0; r2 < size; r2++) for (var c2 = 0; c2 < size; c2++)
        if (!res[r2][c2] && MASKS[mk](r2, c2)) cand[r2][c2] ^= 1;
      placeFormat(cand, mk);
      var sc = penalty(cand);
      if (sc < bestScore) { bestScore = sc; best = cand; }
    }
    return best;
  }

  function svg(text, opts) {
    opts = opts || {};
    var m = matrix(text), n = m.length;
    var quiet = opts.quiet == null ? 3 : opts.quiet;
    var dim = n + quiet * 2;
    var dark = opts.dark || '#07100C', light = opts.light || '#E8F2EC';
    var path = '';
    for (var r = 0; r < n; r++) {
      var c = 0;
      while (c < n) {
        if (m[r][c]) {
          var start = c;
          while (c < n && m[r][c]) c++;
          path += 'M' + (start + quiet) + ' ' + (r + quiet) + 'h' + (c - start) + 'v1h' + -(c - start) + 'z';
        } else c++;
      }
    }
    return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ' + dim + ' ' + dim +
      '" shape-rendering="crispEdges" width="100%" height="100%">' +
      '<rect width="' + dim + '" height="' + dim + '" fill="' + light + '"/>' +
      '<path d="' + path + '" fill="' + dark + '"/></svg>';
  }

  var QR = { matrix: matrix, svg: svg };
  if (typeof module !== 'undefined' && module.exports) module.exports = QR;
  global.QR = QR;
})(typeof window !== 'undefined' ? window : globalThis);
