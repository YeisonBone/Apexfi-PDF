'use strict';

pdfjsLib.GlobalWorkerOptions.workerSrc =
  'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';

const $ = id => document.getElementById(id);
const viewer = $('viewer');
const editor = $('textEditor');
const measure = document.createElement('canvas').getContext('2d');

const FONT = 'Helvetica, Arial, sans-serif';
const LINE = 1.2;     // interlineado, en múltiplos del tamaño de letra
const ASCENT = 0.94;  // distancia de la parte superior de la línea a la línea base

const HINTS = {
  select: 'Haz clic en un elemento para seleccionarlo y arrástralo para moverlo. Doble clic en un texto para editarlo. Supr lo elimina.',
  edittext: 'Haz clic sobre un texto del PDF (recuadros punteados) para reescribirlo. Si lo dejas vacío, el texto se borra.',
  text: 'Haz clic en la página donde quieras escribir.',
  whiteout: 'Arrastra para tapar una zona con un rectángulo blanco.',
  highlight: 'Arrastra sobre la zona que quieras resaltar.',
  rect: 'Arrastra para dibujar un rectángulo.',
  draw: 'Arrastra para dibujar a mano alzada (útil para firmar).',
};

// Estado. Las anotaciones se guardan en coordenadas de la página tal como
// venía en el PDF (escala 1, origen arriba a la izquierda), sin la rotación
// que aplique el usuario.
let sources = [];   // { bytes, doc }
let pages = [];     // { src, idx, rot, anns }
let views = [];     // un elemento por página visible en el DOM
let images = {};    // id -> { url, el }
let imageSeq = 0;
let scale = 1.25;
let tool = 'select';
let sel = null;     // { p, a }
let editing = null; // { v, a }
let drag = null;
let undoStack = [];
let redoStack = [];
let fileName = 'documento';

const infoCache = new Map();

const clamp = (n, lo, hi) => Math.min(hi, Math.max(lo, n));
const viewOf = p => views.find(v => v.p === p);

function pageInfo(p) {
  const key = p.src + ':' + p.idx;
  if (!infoCache.has(key)) {
    infoCache.set(key, sources[p.src].doc.getPage(p.idx + 1)
      .then(page => ({ page, vp: page.getViewport({ scale: 1 }) })));
  }
  return infoCache.get(key);
}

/* ---------- Geometría ---------- */

// Rotación horaria (eje Y hacia abajo) en múltiplos de 90°.
function rotv(rot, x, y) {
  return rot === 90 ? [-y, x] : rot === 180 ? [-x, -y] : rot === 270 ? [y, -x] : [x, y];
}

function toLocal(f, x, y) {
  return rotv((360 - f.rot) % 360, x - f.ox, y - f.oy);
}

function fromLocal(f, lx, ly) {
  const [dx, dy] = rotv(f.rot, lx, ly);
  return [f.ox + dx, f.oy + dy];
}

function toView(v, x, y) {
  const r = v.p.rot;
  const [u, w] = r === 90 ? [v.H - y, x] : r === 180 ? [v.W - x, v.H - y] : r === 270 ? [y, v.W - x] : [x, y];
  return [u * scale, w * scale];
}

function toPage(v, u, w) {
  u /= scale;
  w /= scale;
  const r = v.p.rot;
  return r === 90 ? [w, v.H - u] : r === 180 ? [v.W - u, v.H - w] : r === 270 ? [v.W - w, u] : [u, w];
}

function eventPoint(v, e) {
  const r = v.overlay.getBoundingClientRect();
  return toPage(v, e.clientX - r.left, e.clientY - r.top);
}

// Caja de una anotación: origen, rotación y rectángulo en coordenadas locales.
function frame(a) {
  if (a.type === 'text') {
    measure.font = `${a.size}px ${FONT}`;
    const lines = a.text.split('\n');
    const w = Math.max(10, ...lines.map(l => measure.measureText(l).width));
    return { ox: a.x, oy: a.y, rot: a.rot, x: 0, y: 0, w, h: lines.length * a.size * LINE };
  }
  if (a.type === 'image') return { ox: a.x, oy: a.y, rot: a.rot, x: 0, y: 0, w: a.w, h: a.h };
  if (a.type === 'path') {
    const xs = a.pts.map(p => p[0]), ys = a.pts.map(p => p[1]);
    const pad = a.width / 2 + 2;
    const x = Math.min(...xs) - pad, y = Math.min(...ys) - pad;
    return { ox: 0, oy: 0, rot: 0, x, y, w: Math.max(...xs) + pad - x, h: Math.max(...ys) + pad - y };
  }
  return { ox: 0, oy: 0, rot: 0, x: a.x, y: a.y, w: a.w, h: a.h };
}

function hitAnn(a, x, y) {
  const f = frame(a), pad = 3;
  const [lx, ly] = toLocal(f, x, y);
  return lx >= f.x - pad && lx <= f.x + f.w + pad && ly >= f.y - pad && ly <= f.y + f.h + pad;
}

function hit(p, x, y, type) {
  for (let i = p.anns.length - 1; i >= 0; i--) {
    const a = p.anns[i];
    if ((!type || a.type === type) && hitAnn(a, x, y)) return a;
  }
  return null;
}

const resizable = a => a.type === 'rect' || a.type === 'image';

/* ---------- Deshacer / rehacer ---------- */

function pushUndo() {
  undoStack.push(JSON.stringify(pages));
  if (undoStack.length > 100) undoStack.shift();
  redoStack = [];
  updateUI();
}

function restore(from, to) {
  commitEdit();
  if (!from.length) return;
  to.push(JSON.stringify(pages));
  pages = JSON.parse(from.pop());
  sel = null;
  rebuild();
}

/* ---------- Vista ---------- */

const observer = new IntersectionObserver(entries => {
  for (const e of entries) {
    const v = e.target._v;
    v.visible = e.isIntersecting;
    if (v.visible) {
      renderPage(v);
      drawOverlay(v);
    } else {
      unrender(v);
      v.overlay.width = v.overlay.height = 0;
    }
  }
}, { root: viewer, rootMargin: '600px 0px' });

async function rebuild(scrollRatio = 1) {
  commitEdit();
  const top = viewer.scrollTop;
  const infos = await Promise.all(pages.map(pageInfo));
  observer.disconnect();
  views.forEach(unrender);
  viewer.querySelectorAll('.page-wrap').forEach(n => n.remove());
  views = pages.map((p, i) => makeView(p, i, infos[i]));
  viewer.scrollTop = top * scrollRatio;
  updateUI();
}

function makeView(p, i, info) {
  const W = info.vp.width, H = info.vp.height;
  const side = p.rot % 180 !== 0;
  const v = {
    p, info, W, H,
    vw: (side ? H : W) * scale,
    vh: (side ? W : H) * scale,
    visible: false, want: false, busy: false, done: false, task: null,
  };

  const wrap = document.createElement('div');
  wrap.className = 'page-wrap';

  const head = document.createElement('div');
  head.className = 'page-head';
  const label = document.createElement('span');
  label.textContent = `Página ${i + 1} de ${pages.length}`;
  head.appendChild(label);
  const acts = [
    ['left', '⟲', 'Girar a la izquierda'], ['right', '⟳', 'Girar a la derecha'],
    ['up', '↑', 'Subir página'], ['down', '↓', 'Bajar página'], ['del', '✕', 'Eliminar página'],
  ];
  for (const [act, text, title] of acts) {
    const b = document.createElement('button');
    b.textContent = text;
    b.title = title;
    b.disabled = (act === 'up' && i === 0) || (act === 'down' && i === pages.length - 1) ||
      (act === 'del' && pages.length === 1);
    b.onclick = () => pageAction(p, act);
    head.appendChild(b);
  }

  v.box = document.createElement('div');
  v.box.className = 'page';
  v.box.style.width = v.vw + 'px';
  v.box.style.height = v.vh + 'px';
  v.box._v = v;
  v.canvas = document.createElement('canvas');
  v.overlay = document.createElement('canvas');
  v.overlay.className = 'overlay';
  v.box.append(v.canvas, v.overlay);

  v.overlay.addEventListener('mousedown', e => e.preventDefault());
  v.overlay.addEventListener('pointerdown', e => onDown(v, e));
  v.overlay.addEventListener('pointermove', e => onMove(v, e));
  v.overlay.addEventListener('pointerup', e => onUp(v, e));
  v.overlay.addEventListener('pointercancel', e => onUp(v, e));
  v.overlay.addEventListener('dblclick', e => {
    if (tool !== 'select') return;
    const a = hit(p, ...eventPoint(v, e), 'text');
    if (a) {
      pushUndo();
      startEdit(v, a);
    }
  });

  wrap.append(head, v.box);
  viewer.appendChild(wrap);
  observer.observe(v.box);
  return v;
}

async function renderPage(v) {
  v.want = true;
  if (v.busy) return;
  v.busy = true;
  while (v.want && !v.done) {
    const dpr = window.devicePixelRatio || 1;
    const vp = v.info.page.getViewport({
      scale: scale * dpr,
      rotation: (v.info.vp.rotation + v.p.rot) % 360,
    });
    v.canvas.width = Math.round(vp.width);
    v.canvas.height = Math.round(vp.height);
    v.task = v.info.page.render({ canvasContext: v.canvas.getContext('2d'), viewport: vp });
    try {
      await v.task.promise;
      v.done = true;
    } catch (err) {
      if (!err || err.name !== 'RenderingCancelledException') {
        console.error(err);
        v.done = true;
      }
    }
    v.task = null;
  }
  v.busy = false;
  if (!v.want) clearCanvas(v);
}

function unrender(v) {
  v.want = false;
  if (v.task) v.task.cancel();
  else if (!v.busy) clearCanvas(v);
}

function clearCanvas(v) {
  v.canvas.width = v.canvas.height = 0;
  v.done = false;
}

function drawOverlay(v) {
  if (!v.visible) return;
  const dpr = window.devicePixelRatio || 1;
  const c = v.overlay, ctx = c.getContext('2d');
  const cw = Math.round(v.vw * dpr), ch = Math.round(v.vh * dpr);
  if (c.width !== cw || c.height !== ch) {
    c.width = cw;
    c.height = ch;
  }
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, cw, ch);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const r = v.p.rot;
  ctx.translate(r === 90 || r === 180 ? v.vw : 0, r === 180 || r === 270 ? v.vh : 0);
  ctx.rotate(r * Math.PI / 180);
  ctx.scale(scale, scale);

  for (const a of v.p.anns) drawAnn(ctx, a);

  if (tool === 'edittext') {
    if (!v.info.items) loadText(v);
    else {
      ctx.strokeStyle = 'rgba(47, 111, 237, .55)';
      ctx.lineWidth = 1 / scale;
      ctx.setLineDash([3 / scale, 3 / scale]);
      for (const it of v.info.items) {
        ctx.strokeRect(it.box.x, it.box.y, it.box.w, it.box.h);
      }
      ctx.setLineDash([]);
    }
  }

  if (sel && sel.p === v.p && !editing) {
    const f = frame(sel.a);
    ctx.save();
    ctx.translate(f.ox, f.oy);
    ctx.rotate(f.rot * Math.PI / 180);
    ctx.strokeStyle = '#2f6fed';
    ctx.lineWidth = 1.5 / scale;
    ctx.setLineDash([4 / scale, 3 / scale]);
    ctx.strokeRect(f.x - 2, f.y - 2, f.w + 4, f.h + 4);
    if (resizable(sel.a)) {
      const s = 8 / scale;
      ctx.setLineDash([]);
      ctx.fillStyle = '#2f6fed';
      ctx.fillRect(f.x + f.w - s / 2, f.y + f.h - s / 2, s, s);
    }
    ctx.restore();
  }
}

function drawAnn(ctx, a) {
  if (a.type === 'text') {
    if (a.cover) {
      ctx.fillStyle = a.cover.color;
      ctx.fillRect(a.cover.x, a.cover.y, a.cover.w, a.cover.h);
    }
    if (editing && editing.a === a) return;
    ctx.save();
    ctx.translate(a.x, a.y);
    ctx.rotate(a.rot * Math.PI / 180);
    ctx.fillStyle = a.color;
    ctx.font = `${a.size}px ${FONT}`;
    ctx.textBaseline = 'alphabetic';
    a.text.split('\n').forEach((l, i) => ctx.fillText(l, 0, a.size * (ASCENT + i * LINE)));
    ctx.restore();
  } else if (a.type === 'rect') {
    if (a.fill) {
      ctx.globalAlpha = a.alpha;
      ctx.fillStyle = a.fill;
      ctx.fillRect(a.x, a.y, a.w, a.h);
      ctx.globalAlpha = 1;
    } else {
      ctx.strokeStyle = a.color;
      ctx.lineWidth = a.width;
      ctx.strokeRect(a.x, a.y, a.w, a.h);
    }
  } else if (a.type === 'path') {
    ctx.strokeStyle = a.color;
    ctx.lineWidth = a.width;
    ctx.lineCap = ctx.lineJoin = 'round';
    ctx.beginPath();
    ctx.moveTo(a.pts[0][0], a.pts[0][1]);
    for (const [x, y] of a.pts) ctx.lineTo(x, y);
    ctx.stroke();
  } else if (a.type === 'image') {
    ctx.save();
    ctx.translate(a.x, a.y);
    ctx.rotate(a.rot * Math.PI / 180);
    ctx.drawImage(images[a.img].el, 0, 0, a.w, a.h);
    ctx.restore();
  }
}

/* ---------- Texto existente del PDF ---------- */

// Reúne el texto editable de la página: el del contenido y el de las
// anotaciones de texto (FreeText) que añaden otros editores de PDF.
function loadText(v) {
  const info = v.info;
  if (!info.itemsPromise) {
    info.itemsPromise = Promise.all([info.page.getTextContent(), info.page.getAnnotations()]).then(([tc, annots]) => {
      const items = [];
      for (const it of tc.items) {
        if (!it.str || !it.str.trim()) continue;
        const t = pdfjsLib.Util.transform(info.vp.transform, it.transform);
        const raw = Math.hypot(t[2], t[3]);
        const deg = Math.atan2(t[1], t[0]) * 180 / Math.PI;
        const rot = ((Math.round(deg / 90) * 90) % 360 + 360) % 360;
        // Solo texto horizontal o girado en múltiplos de 90°.
        if (raw < 1 || Math.abs(deg - Math.round(deg / 90) * 90) > 1) continue;
        const base = { ox: t[4], oy: t[5], rot };
        const [x1, y1] = fromLocal(base, -1, -raw * 0.9);
        const [x2, y2] = fromLocal(base, it.width + 1, raw * 0.3);
        const size = Math.round(raw * 10) / 10;
        const [x, y] = fromLocal(base, 0, -size * ASCENT);
        items.push({
          str: it.str, x, y, rot, size, color: '#000000',
          box: { x: Math.min(x1, x2), y: Math.min(y1, y2), w: Math.abs(x2 - x1), h: Math.abs(y2 - y1) },
        });
      }
      for (const an of annots) {
        if (an.subtype !== 'FreeText' || !an.rect) continue;
        const lines = an.textContent && an.textContent.length
          ? an.textContent
          : ((an.contentsObj && an.contentsObj.str) || '').split(/\r\n?|\n/);
        const str = lines.join('\n').replace(/\s+$/, '');
        if (!str.trim()) continue;
        const r = info.vp.convertToViewportRectangle(an.rect);
        const box = { x: Math.min(r[0], r[2]), y: Math.min(r[1], r[3]), w: Math.abs(r[2] - r[0]), h: Math.abs(r[3] - r[1]) };
        const rot = ((info.vp.rotation - (an.rotation || 0)) % 360 + 360) % 360;
        const da = an.defaultAppearanceData || {};
        const c = da.fontColor;
        // El texto empieza en la esquina de la caja que queda arriba a la izquierda al leerlo.
        const corner = {
          ox: rot === 90 || rot === 180 ? box.x + box.w : box.x,
          oy: rot === 180 || rot === 270 ? box.y + box.h : box.y,
          rot,
        };
        const [x, y] = fromLocal(corner, 2, 1);
        items.push({
          str, x, y, rot, box,
          size: Math.round((da.fontSize || 12) * 10) / 10,
          color: c ? '#' + Array.from(c).slice(0, 3).map(n => n.toString(16).padStart(2, '0')).join('') : '#000000',
          annotRect: Array.from(an.rect),
        });
      }
      info.items = items;
    }).catch(err => {
      console.error(err);
      info.items = [];
    });
  }
  info.itemsPromise.then(() => {
    if (tool === 'edittext') drawOverlay(v);
  });
}

// Lo último que se dibuja queda encima, así que se busca desde el final.
function itemAt(v, x, y) {
  const items = v.info.items || [];
  for (let i = items.length - 1; i >= 0; i--) {
    const b = items[i].box;
    if (x >= b.x && x <= b.x + b.w && y >= b.y && y <= b.y + b.h) return items[i];
  }
  return null;
}

// Color de fondo más frecuente justo fuera de las esquinas de una zona.
function sampleColor(v, c) {
  const counts = {};
  let best = '#ffffff';
  try {
    const ctx = v.canvas.getContext('2d');
    const k = v.canvas.width / v.vw;
    const pts = [[c.x - 1, c.y - 1], [c.x + c.w + 1, c.y - 1], [c.x - 1, c.y + c.h + 1], [c.x + c.w + 1, c.y + c.h + 1]];
    for (const [x, y] of pts) {
      const [u, w] = toView(v, x, y);
      const d = ctx.getImageData(Math.round(u * k), Math.round(w * k), 1, 1).data;
      if (!d[3]) continue;
      const hex = '#' + [d[0], d[1], d[2]].map(n => n.toString(16).padStart(2, '0')).join('');
      counts[hex] = (counts[hex] || 0) + 1;
      if (counts[hex] > (counts[best] || 0)) best = hex;
    }
  } catch (err) { /* lienzo aún sin dibujar */ }
  return best;
}

function annFromItem(v, it) {
  const cover = { ...it.box, color: sampleColor(v, it.box) };
  const a = { type: 'text', x: it.x, y: it.y, rot: it.rot, size: it.size, color: it.color, text: it.str, cover };
  if (it.annotRect) {
    // Al guardar se quita la anotación original, así que el parche solo hace falta en pantalla.
    a.annotRect = it.annotRect;
    cover.screenOnly = true;
  }
  return a;
}

/* ---------- Edición de texto ---------- */

function startEdit(v, a) {
  editing = { v, a };
  sel = { p: v.p, a };
  v.box.appendChild(editor);
  editor.value = a.text;
  const [u, w] = toView(v, a.x, a.y);
  Object.assign(editor.style, {
    display: 'block',
    left: u + 'px',
    top: w + 'px',
    fontSize: a.size * scale + 'px',
    color: a.color,
  });
  sizeEditor();
  drawOverlay(v);
  editor.focus();
  updateUI();
}

function sizeEditor() {
  const { a } = editing;
  a.text = editor.value;
  const f = frame(a);
  editor.style.width = f.w * scale + 24 + 'px';
  editor.style.height = f.h * scale + 4 + 'px';
}

function commitEdit() {
  if (!editing) return;
  const { v, a } = editing;
  editing = null;
  a.text = editor.value.replace(/\s+$/, '');
  editor.style.display = 'none';
  if (!a.text && !a.cover) {
    v.p.anns.splice(v.p.anns.indexOf(a), 1);
    sel = null;
  }
  drawOverlay(v);
  updateUI();
}

editor.addEventListener('input', sizeEditor);
editor.addEventListener('blur', commitEdit);
editor.addEventListener('keydown', e => {
  if (e.key === 'Escape') commitEdit();
});

/* ---------- Ratón / táctil ---------- */

const fontSize = () => clamp(+$('fontSize').value || 14, 4, 200);
const strokeWidth = () => clamp(+$('stroke').value || 2, 1, 40);

function select(s) {
  sel = s;
  if (s) {
    const a = s.a;
    if (a.color) $('color').value = a.color;
    if (a.type === 'text') $('fontSize').value = a.size;
    if (a.width) $('stroke').value = a.width;
  }
  updateUI();
}

function onDown(v, e) {
  if (e.button) return;
  const wasEditing = editing;
  commitEdit();
  const p = v.p;
  const [x, y] = eventPoint(v, e);
  const prevSel = sel;

  if (tool === 'select') {
    let mode = 'move', a = null;
    if (sel && sel.p === p && resizable(sel.a)) {
      const f = frame(sel.a);
      const [lx, ly] = toLocal(f, x, y);
      const r = 8 / scale;
      if (Math.abs(lx - f.x - f.w) <= r && Math.abs(ly - f.y - f.h) <= r) {
        mode = 'resize';
        a = sel.a;
      }
    }
    if (!a) a = hit(p, x, y);
    select(a ? { p, a } : null);
    if (a) drag = { mode, a, x, y, moved: false, ratio: a.h / a.w };
  } else if (tool === 'text' || tool === 'edittext') {
    if (wasEditing) return;
    let a = tool === 'edittext' ? hit(p, x, y, 'text') : null;
    if (!a) {
      const it = tool === 'edittext' && itemAt(v, x, y);
      if (tool === 'edittext' && !it) return;
      a = it ? annFromItem(v, it)
        : { type: 'text', x, y, rot: (360 - p.rot) % 360, size: fontSize(), color: $('color').value, text: '' };
      pushUndo();
      p.anns.push(a);
    } else {
      pushUndo();
    }
    startEdit(v, a);
    return;
  } else if (tool === 'draw') {
    pushUndo();
    const a = { type: 'path', pts: [[x, y]], color: $('color').value, width: strokeWidth() };
    p.anns.push(a);
    drag = { mode: 'draw', a };
  } else {
    pushUndo();
    const a = { type: 'rect', x, y, w: 0, h: 0 };
    if (tool === 'whiteout') Object.assign(a, { fill: '#ffffff', alpha: 1 });
    else if (tool === 'highlight') Object.assign(a, { fill: '#ffe600', alpha: 0.4 });
    else Object.assign(a, { color: $('color').value, width: strokeWidth() });
    p.anns.push(a);
    drag = { mode: 'new', a, x, y };
  }

  if (drag) v.overlay.setPointerCapture(e.pointerId);
  drawOverlay(v);
  if (prevSel && prevSel.p !== p) {
    const pv = viewOf(prevSel.p);
    if (pv) drawOverlay(pv);
  }
}

function onMove(v, e) {
  if (!drag) return;
  const [x, y] = eventPoint(v, e);
  const a = drag.a;
  if (drag.mode === 'draw') {
    a.pts.push([x, y]);
  } else if (drag.mode === 'new') {
    a.x = Math.min(drag.x, x);
    a.y = Math.min(drag.y, y);
    a.w = Math.abs(x - drag.x);
    a.h = Math.abs(y - drag.y);
  } else {
    if (!drag.moved) {
      pushUndo();
      drag.moved = true;
    }
    if (drag.mode === 'move') {
      const dx = x - drag.x, dy = y - drag.y;
      if (a.type === 'path') a.pts.forEach(pt => { pt[0] += dx; pt[1] += dy; });
      else { a.x += dx; a.y += dy; }
      drag.x = x;
      drag.y = y;
    } else {
      const f = frame(a);
      const [lx, ly] = toLocal(f, x, y);
      a.w = Math.max(5, lx - f.x);
      a.h = a.type === 'image' ? a.w * drag.ratio : Math.max(5, ly - f.y);
    }
  }
  drawOverlay(v);
}

function onUp(v) {
  if (!drag) return;
  const { mode, a } = drag;
  drag = null;
  if (mode === 'new' && (a.w < 3 || a.h < 3)) {
    v.p.anns.splice(v.p.anns.indexOf(a), 1);
    undoStack.pop();
  }
  drawOverlay(v);
  updateUI();
}

/* ---------- Acciones ---------- */

function setTool(t) {
  commitEdit();
  tool = t;
  if (t !== 'select') sel = null;
  viewer.dataset.tool = t;
  views.forEach(drawOverlay);
  updateUI();
}

function pageAction(p, act) {
  commitEdit();
  const i = pages.indexOf(p);
  if (i < 0) return;
  pushUndo();
  if (act === 'left') p.rot = (p.rot + 270) % 360;
  else if (act === 'right') p.rot = (p.rot + 90) % 360;
  else if (act === 'up') pages.splice(i - 1, 2, p, pages[i - 1]);
  else if (act === 'down') pages.splice(i, 2, pages[i + 1], p);
  else if (act === 'del') {
    pages.splice(i, 1);
    if (sel && sel.p === p) sel = null;
  }
  rebuild();
}

function deleteSelection() {
  if (!sel || editing) return;
  pushUndo();
  sel.p.anns.splice(sel.p.anns.indexOf(sel.a), 1);
  const v = viewOf(sel.p);
  sel = null;
  if (v) drawOverlay(v);
  updateUI();
}

function applyStyle(fn) {
  if (!sel || editing) return;
  pushUndo();
  fn(sel.a);
  const v = viewOf(sel.p);
  if (v) drawOverlay(v);
}

function setScale(s) {
  const old = scale;
  scale = clamp(Math.round(s * 100) / 100, 0.25, 4);
  if (scale !== old) rebuild(scale / old);
}

function currentView() {
  const mid = viewer.getBoundingClientRect().top + viewer.clientHeight / 2;
  return views.find(v => v.box.getBoundingClientRect().bottom > mid) || views[views.length - 1];
}

async function openPdf(file, replace) {
  try {
    const bytes = new Uint8Array(await file.arrayBuffer());
    // pdf.js se queda con el buffer que recibe, así que le pasamos una copia.
    const doc = await pdfjsLib.getDocument({ data: bytes.slice() }).promise;
    commitEdit();
    if (replace) {
      sources = [];
      pages = [];
      infoCache.clear();
      undoStack = [];
      redoStack = [];
      sel = null;
      fileName = file.name.replace(/\.pdf$/i, '');
    } else {
      pushUndo();
    }
    const src = sources.push({ bytes, doc }) - 1;
    for (let i = 0; i < doc.numPages; i++) pages.push({ src, idx: i, rot: 0, anns: [] });
    if (replace) {
      const { vp } = await pageInfo(pages[0]);
      scale = clamp(Math.floor((viewer.clientWidth - 60) / vp.width * 20) / 20, 0.5, 1.5);
      viewer.scrollTop = 0;
    }
    await rebuild();
  } catch (err) {
    console.error(err);
    alert(err && err.name === 'PasswordException'
      ? 'Este PDF está protegido con contraseña y no se puede abrir.'
      : 'No se pudo abrir el PDF: ' + (err && err.message || err));
  }
}

function addImage(file) {
  const reader = new FileReader();
  reader.onload = () => {
    const el = new Image();
    el.onload = () => {
      let url = reader.result;
      if (!/^data:image\/(png|jpeg)/.test(url)) {
        const c = document.createElement('canvas');
        c.width = el.naturalWidth;
        c.height = el.naturalHeight;
        c.getContext('2d').drawImage(el, 0, 0);
        url = c.toDataURL('image/png');
      }
      const v = currentView();
      if (!v) return;
      const id = 'img' + (++imageSeq);
      images[id] = { url, el };

      // Tamaño inicial: como mucho el 40 % del lado visible de la página.
      const side = v.p.rot % 180 !== 0;
      const maxW = (side ? v.H : v.W) * 0.4, maxH = (side ? v.W : v.H) * 0.4;
      const k = Math.min(1, maxW / el.naturalWidth, maxH / el.naturalHeight);
      const w = el.naturalWidth * k, h = el.naturalHeight * k;

      // Centrada en la parte de la página que se está viendo.
      const br = v.box.getBoundingClientRect(), vr = viewer.getBoundingClientRect();
      const [cx, cy] = toPage(v,
        clamp(vr.left + vr.width / 2 - br.left, 0, v.vw),
        clamp(vr.top + vr.height / 2 - br.top, 0, v.vh));
      const rot = (360 - v.p.rot) % 360;
      const [x, y] = fromLocal({ ox: cx, oy: cy, rot }, -w / 2, -h / 2);

      pushUndo();
      const a = { type: 'image', img: id, x, y, w, h, rot };
      v.p.anns.push(a);
      setTool('select');
      select({ p: v.p, a });
      drawOverlay(v);
    };
    el.onerror = () => alert('No se pudo leer la imagen.');
    el.src = reader.result;
  };
  reader.readAsDataURL(file);
}

/* ---------- Guardar ---------- */

async function buildPdf() {
  const { PDFDocument, PDFDict, PDFArray, PDFName, StandardFonts, rgb, degrees, LineCapStyle } = PDFLib;
  const out = await PDFDocument.create();
  const font = await out.embedFont(StandardFonts.Helvetica);
  const color = h => rgb(parseInt(h.slice(1, 3), 16) / 255, parseInt(h.slice(3, 5), 16) / 255, parseInt(h.slice(5, 7), 16) / 255);
  // Las fuentes estándar solo admiten WinAnsi; se descartan los demás caracteres.
  const encodable = s => [...s].filter(ch => {
    try { font.encodeText(ch); return true; } catch (err) { return false; }
  }).join('');

  // Se copian de una vez todas las páginas de cada origen para no duplicar recursos.
  const copies = new Map();
  for (let s = 0; s < sources.length; s++) {
    const used = pages.filter(p => p.src === s);
    if (!used.length) continue;
    const doc = await PDFDocument.load(sources[s].bytes, { ignoreEncryption: true });
    if (doc.isEncrypted) throw new Error('el PDF está cifrado y no se puede guardar modificado.');
    const copied = await out.copyPages(doc, used.map(p => p.idx));
    used.forEach((p, i) => copies.set(p, copied[i]));
  }

  const embedded = {};
  for (const p of pages) {
    const pg = out.addPage(copies.get(p));
    const { vp } = await pageInfo(p);
    pg.setRotation(degrees((vp.rotation + p.rot) % 360));
    if (!p.anns.length) continue;

    // Quita las anotaciones de texto originales que se han reescrito.
    const gone = p.anns.filter(a => a.annotRect).map(a => a.annotRect);
    const annots = gone.length && pg.node.Annots();
    for (let i = annots ? annots.size() - 1 : -1; i >= 0; i--) {
      try {
        const d = annots.lookup(i);
        if (!(d instanceof PDFDict) || d.get(PDFName.of('Subtype')) !== PDFName.of('FreeText')) continue;
        const r = d.lookup(PDFName.of('Rect'), PDFArray).asArray().map(n => out.context.lookup(n).asNumber());
        const rect = [Math.min(r[0], r[2]), Math.min(r[1], r[3]), Math.max(r[0], r[2]), Math.max(r[1], r[3])];
        if (gone.some(g => g.every((n, k) => Math.abs(n - rect[k]) < 0.01))) annots.remove(i);
      } catch (err) { console.warn(err); }
    }

    // Aísla el contenido original para que su estado gráfico no afecte a lo añadido.
    try {
      pg.node.normalize();
      pg.node.wrapContentStreams(
        out.context.getPushGraphicsStateContentStream(),
        out.context.getPopGraphicsStateContentStream());
    } catch (err) { console.warn(err); }

    const pt = (x, y) => {
      const [px, py] = vp.convertToPdfPoint(x, y);
      return { x: px, y: py };
    };
    const box = r => {
      const a = pt(r.x, r.y), b = pt(r.x + r.w, r.y + r.h);
      return { x: Math.min(a.x, b.x), y: Math.min(a.y, b.y), width: Math.abs(b.x - a.x), height: Math.abs(b.y - a.y) };
    };
    // Giro (antihorario, en el espacio del PDF) para que el elemento se vea como en pantalla.
    const turn = a => degrees((vp.rotation - a.rot + 360) % 360);

    for (const a of p.anns) {
      if (a.type === 'text') {
        if (a.cover && !a.cover.screenOnly) pg.drawRectangle({ ...box(a.cover), color: color(a.cover.color) });
        const f = frame(a);
        a.text.split('\n').forEach((line, i) => {
          line = encodable(line);
          if (!line.trim()) return;
          pg.drawText(line, {
            ...pt(...fromLocal(f, 0, a.size * (ASCENT + i * LINE))),
            size: a.size, font, color: color(a.color), rotate: turn(a),
          });
        });
      } else if (a.type === 'rect') {
        if (a.fill) pg.drawRectangle({ ...box(a), color: color(a.fill), opacity: a.alpha });
        else pg.drawRectangle({ ...box(a), borderColor: color(a.color), borderWidth: a.width });
      } else if (a.type === 'path') {
        const pts = a.pts.map(q => pt(q[0], q[1]));
        for (let i = 1; i < Math.max(2, pts.length); i++) {
          pg.drawLine({
            start: pts[i - 1], end: pts[Math.min(i, pts.length - 1)],
            thickness: a.width, color: color(a.color), lineCap: LineCapStyle.Round,
          });
        }
      } else if (a.type === 'image') {
        const url = images[a.img].url;
        if (!embedded[a.img]) {
          embedded[a.img] = await (url.startsWith('data:image/png') ? out.embedPng(url) : out.embedJpg(url));
        }
        pg.drawImage(embedded[a.img], {
          ...pt(...fromLocal(frame(a), 0, a.h)),
          width: a.w, height: a.h, rotate: turn(a),
        });
      }
    }
  }
  return out.save();
}

async function save() {
  commitEdit();
  const btn = $('btnSave');
  btn.disabled = true;
  btn.textContent = 'Guardando…';
  try {
    const bytes = await buildPdf();
    const url = URL.createObjectURL(new Blob([bytes], { type: 'application/pdf' }));
    const link = document.createElement('a');
    link.href = url;
    link.download = fileName + '-editado.pdf';
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 10000);
  } catch (err) {
    console.error(err);
    alert('Error al guardar: ' + (err && err.message || err));
  }
  btn.textContent = 'Guardar';
  updateUI();
}

/* ---------- Interfaz ---------- */

function updateUI() {
  const has = pages.length > 0;
  document.querySelectorAll('.needs-doc').forEach(b => { b.disabled = !has; });
  document.querySelectorAll('#tools [data-tool]').forEach(b => b.classList.toggle('active', has && b.dataset.tool === tool));
  $('btnUndo').disabled = !undoStack.length;
  $('btnRedo').disabled = !redoStack.length;
  $('btnDelete').disabled = !sel || !!editing;
  $('zoomLabel').textContent = Math.round(scale * 100) + '%';
  $('empty').style.display = has ? 'none' : '';
  $('hint').textContent = has ? HINTS[tool] : '';
}

$('btnOpen').onclick = () => { $('fileInput').dataset.replace = '1'; $('fileInput').click(); };
$('btnAdd').onclick = () => { $('fileInput').dataset.replace = ''; $('fileInput').click(); };
$('fileInput').onchange = e => {
  const file = e.target.files[0];
  e.target.value = '';
  if (file) openPdf(file, !!e.target.dataset.replace);
};
$('btnImage').onclick = () => $('imgInput').click();
$('imgInput').onchange = e => {
  const file = e.target.files[0];
  e.target.value = '';
  if (file) addImage(file);
};
$('btnSave').onclick = save;
$('btnUndo').onclick = () => restore(undoStack, redoStack);
$('btnRedo').onclick = () => restore(redoStack, undoStack);
$('btnDelete').onclick = deleteSelection;
$('zoomIn').onclick = () => setScale(scale + 0.25);
$('zoomOut').onclick = () => setScale(scale - 0.25);
document.querySelectorAll('#tools [data-tool]').forEach(b => { b.onclick = () => setTool(b.dataset.tool); });

$('color').onchange = () => applyStyle(a => { if (a.color) a.color = $('color').value; });
$('fontSize').onchange = () => applyStyle(a => { if (a.type === 'text') a.size = fontSize(); });
$('stroke').onchange = () => applyStyle(a => { if (a.width) a.width = strokeWidth(); });

document.addEventListener('keydown', e => {
  if (/^(INPUT|TEXTAREA)$/.test(e.target.tagName)) return;
  const ctrl = e.ctrlKey || e.metaKey;
  if (e.key === 'Delete' || e.key === 'Backspace') {
    if (sel) e.preventDefault();
    deleteSelection();
  } else if (ctrl && e.key.toLowerCase() === 'z') {
    e.preventDefault();
    if (e.shiftKey) restore(redoStack, undoStack);
    else restore(undoStack, redoStack);
  } else if (ctrl && e.key.toLowerCase() === 'y') {
    e.preventDefault();
    restore(redoStack, undoStack);
  } else if (ctrl && e.key.toLowerCase() === 's') {
    e.preventDefault();
    if (pages.length) save();
  } else if (e.key === 'Escape' && sel) {
    const v = viewOf(sel.p);
    sel = null;
    if (v) drawOverlay(v);
    updateUI();
  }
});

viewer.addEventListener('dragover', e => {
  e.preventDefault();
  viewer.classList.add('dragover');
});
viewer.addEventListener('dragleave', () => viewer.classList.remove('dragover'));
viewer.addEventListener('drop', e => {
  e.preventDefault();
  viewer.classList.remove('dragover');
  const file = [...e.dataTransfer.files].find(f => /\.pdf$/i.test(f.name) || f.type === 'application/pdf');
  if (file) openPdf(file, !pages.length);
});

updateUI();
