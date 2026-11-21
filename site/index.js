// recursion.fast: the home page (the track tabs with each track's record, progression and
// leaderboard; the queue; every submission).
'use strict';
(function () {
  const { el, svg, ext, page, link, fmtS, fmtPart, fmtDate, timeEl, ago, badge, evaluatedAt, gainOf, marginText, pct, unverified,
    scoreIn, retiredIn, trackOf } = window.RF;

  // the record an entry beat in the track, in words: its gain and a link to that record
  function beat(e, tr, data, nm) {
    const a = e.against[tr.id];
    if (!a || !e.record_of[tr.id]) return e.port_of ? 'none (the record re-run at a new pin)' : 'none (no record stood in this track at its pin)';
    const prev = data.subs.find(x => x.id === a.record);
    const name = el('a', { href: page('submission.html', { id: a.record }) }, prev ? nm(prev) : a.record);
    return [pct(gainOf(e, tr.id)), ' against ', name, a.S_record !== null ? ` (${fmtS(a.S_record, unitOf(e, tr))} ${unitOf(e, tr)})` : ''];
  }
  const short = sha => sha ? sha.slice(0, 7) : 'unknown';
  // the unit of an entry's score in a track, by how its result is priced (this season: s\u00b7B)
  const unitOf = (e, tr) => window.RF.pricedBy(tr, window.RF.partsIn(e.score, tr.id)).unit;

  // ---- the track tabs (keyboard: arrows, Home, End; the choice is remembered) --------------------
  let track = window.RF.chosenTrack();
  function tabs(onChange) {
    const list = document.getElementById('track-tabs');
    const all = [...list.querySelectorAll('[role="tab"]')];
    const show = id => {
      for (const b of all) {
        const on = b.getAttribute('data-track') === id;
        b.setAttribute('aria-selected', String(on));
        b.tabIndex = on ? 0 : -1;
        if (on) document.getElementById('track-panel').setAttribute('aria-labelledby', b.id);
      }
      document.getElementById('track-blurb').textContent = trackOf(id).blurb;
    };
    const pick = (id, focus) => {
      if (id === track) { if (focus) all.find(b => b.getAttribute('data-track') === id).focus(); return; }
      track = id;
      window.RF.rememberTrack(id);
      show(id);
      if (focus) all.find(b => b.getAttribute('data-track') === id).focus();
      onChange();
    };
    for (const b of all) b.addEventListener('click', () => pick(b.getAttribute('data-track'), false));
    list.addEventListener('keydown', ev => {
      const i = all.indexOf(document.activeElement);
      if (i < 0) return;
      const to = { ArrowRight: i + 1, ArrowLeft: i - 1, Home: 0, End: all.length - 1 }[ev.key];
      if (to === undefined) return;
      ev.preventDefault();
      pick(all[(to + all.length) % all.length].getAttribute('data-track'), true);
    });
    show(track);
  }

  // ---- record card: the bot's standing record of the track (`record` in submissions.json) ---------
  function recordCard(recs, tr, data, nm) {
    const box = document.getElementById('record');
    box.replaceChildren();
    const cur = data.record[tr.id];
    if (!cur) {
      const waiting = data.subs.filter(e => ['queued', 'running'].includes(e.status)).length;
      const last = recs[recs.length - 1];
      box.append(el('div', { class: 'empty-card' },
        el('h2', null, last ? `No standing ${tr.label.toLowerCase()} record at this contract pin.` : `No ${tr.label.toLowerCase()} record yet. Be the first.`),
        last ? el('p', null, `The records of this track so far were set at earlier pins or retired (the leaderboard keeps them). The first certified, comparable, attested ACCEPT at pin ${short(data.core)} becomes the record of this track once its confirmation run (the same commit, once more at the pin) is one too; the record keeps the worse of the two runs.`)
          : el('p', null, `The first entry with a certified, comparable, attested ACCEPT becomes the record of each track once its confirmation run (the same commit, once more at the pin) is one too, keeping the worse of the two runs. After that, a new record of this track needs a score ${tr.sym} more than ${marginText(data)} below the standing record's, at the same contract pin, in both runs.`),
        data.unpublished ? el('p', null, 'Nothing has been published yet: the first pull request starts the record book.') : null,
        waiting ? el('p', null, waiting === 1 ? 'One submission is in the queue.' : waiting + ' submissions are in the queue.') : null,
        el('div', { class: 'actions' },
          el('a', { class: 'button', href: page('rules.html') + '#submit' }, 'How to submit'),
          el('a', { class: 'button ghost', href: page('rules.html') + '#score' }, 'How the tracks score'))));
      return;
    }
    const sc = window.RF.partsIn(cur.score, tr.id);     // this track's run's parts (a confirmed record)
    // this track's own priced proof (`final`: the final proof; `every`: the largest), its size in
    // bytes the factor (an earlier v6 season's result: its exponential factor of that size)
    const pt = window.RF.pricedBy(tr, sc), [sk, sl] = pt.size;
    const split = [el('span', { class: 'math' }, 'P_total'), fmtS(sc.P_total_s) + '\u00a0s', el('span', { class: 'op' }, '\u00d7'),
      ...(pt.old ? [el('span', { class: 'math' }, pt.factorText), fmtPart(sc[pt.factor], ''), el('span', { class: 'muted' }, ` (${sl} = ${window.RF.fmtBytes(sc[sk])})`)]
        : [el('span', { class: 'math' }, sl), fmtPart(sc[sk], 'B')])];
    const other = window.RF.TRACKS.filter(t => t.id !== tr.id && data.record[t.id] && data.record[t.id].id === cur.id);
    const left = el('div', null,
      el('h2', null, `Current ${tr.label.toLowerCase()} record`),
      el('p', { class: 'score-big' }, el('span', { class: 'math' }, pt.sym), fmtS(scoreIn(cur, tr.id), pt.unit), el('span', { class: 'unit' }, window.RF.unitNode(pt.unit))),
      el('p', { class: 'score-split' }, '=', split),
      el('p', { class: 'score-note' }, pt.note),
      other.length ? el('p', { class: 'score-note' }, 'It also holds the ' + other.map(t => t.label.toLowerCase()).join(' and ') + ' record.') : null);
    const dl = el('dl', { class: 'kv' },
      el('dt', null, 'Entry'), el('dd', null, el('a', { href: page('submission.html', { id: cur.id }) }, nm(cur))),
      el('dt', null, 'Author'), el('dd', null, cur.author ? ext(link.author(cur), cur.author) : '–'),
      cur.agent ? el('dt', null, 'Agent') : null, cur.agent ? el('dd', null, cur.agent) : null,
      el('dt', null, 'Date'), el('dd', null, timeEl(evaluatedAt(cur))),
      el('dt', null, 'Gain'), el('dd', null, beat(cur, tr, data, nm)),
      el('dt', null, 'Contract pin'), el('dd', null, cur.harness_commit ? ext(link.core(cur.harness_commit), short(cur.harness_commit)) : '–'));
    const right = el('div', { class: 'facts' }, dl,
      el('p', { class: 'more' }, el('a', { href: page('submission.html', { id: cur.id }) }, 'Verdict, notes and code'), ' ',
        el('span', { class: 'muted' }, '(pull request '), ext(link.pr(cur), '#' + cur.pr), el('span', { class: 'muted' }, ')')));
    box.append(el('div', { class: 'record' }, left, right));
  }

  // ---- progression chart ----------------------------------------------------------------------
  function niceStep(span, n) {
    const raw = span / n, p = 10 ** Math.floor(Math.log10(raw)), f = raw / p;
    return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p;
  }
  // a tick of the score axis, compact on the axis only (s\u00b7B scores run to 10^9 and beyond:
  // "1.4G", "650M", so the labels leave the plot its width); the tooltip and labels keep fmtS
  const SI = ['', 'k', 'M', 'G', 'T', 'P', 'E'];
  const compact = v => {
    let k = 0, w = v;
    while (+w.toPrecision(3) >= 1000 && k < SI.length - 1) { w /= 1000; k++; }
    return +w.toPrecision(3) >= 1000 ? v.toExponential(1) : String(+w.toPrecision(3)) + SI[k];
  };
  const tickText = (v, u) => v >= 1000 ? compact(v) : v >= 1 || v === 0 ? fmtS(v, u) : v.toExponential(0);
  function chart(recs, tr, data, nm) {
    const box = document.getElementById('chart');
    const S = e => scoreIn(e, tr.id);
    // one axis, one unit: only results priced like this track (s\u00b7B); an earlier v6 season's
    // (seconds, its exponential factor) stay out of the chart, in the tables with their own unit
    const priced = e => !window.RF.pricedBy(tr, window.RF.partsIn(e.score, tr.id)).old;
    // comparable, attested ACCEPTs that are not a record of this track
    const others = data.subs.filter(e => ['accepted', 'record', 'retired'].includes(e.status) && !e.record_in.includes(tr.id)
      && e.verified && e.comparable && S(e) !== null && evaluatedAt(e) && priced(e));
    const W = Math.max(280, box.clientWidth - 16), H = W < 560 ? 240 : 300;
    const m = { l: 50, r: W < 560 ? 52 : 70, t: 18, b: 30 };
    const pos = recs.filter(priced), earlier = recs.length - pos.length;
    const u = tr.unit;
    const s = svg('svg', { viewBox: `0 0 ${W} ${H}`, role: 'img', 'aria-label': pos.length
      ? `${tr.label} record score over time: ${pos.length} records, from ${fmtS(S(pos[0]), u)} ${u} to ${fmtS(S(pos[pos.length - 1]), u)} ${u}`
      : earlier ? `No ${tr.label.toLowerCase()} records at this season's rule yet` : `No ${tr.label.toLowerCase()} records yet` });
    const tip = el('div', { class: 'tooltip', hidden: true, role: 'status' });
    box.replaceChildren();
    const note = earlier ? el('div', { class: 'legend' }, el('span', { class: 'muted' }, earlier === 1
      ? `One earlier record, priced by an earlier season's rule (in seconds), is not charted; the leaderboard lists it.`
      : `${earlier} earlier records, priced by an earlier season's rule (in seconds), are not charted; the leaderboard lists them.`)) : null;
    if (!pos.length) {
      for (let i = 0; i < 5; i++) s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: m.t + i * (H - m.t - m.b) / 4, y2: m.t + i * (H - m.t - m.b) / 4 }));
      s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
      s.append(svg('text', { class: 'empty-msg', x: (m.l + W - m.r) / 2, y: (H - m.b + m.t) / 2, 'text-anchor': 'middle' },
        earlier ? 'The first record at this season\'s rule will start this line.' : 'The first record of this track will start this line.'));
      box.append(s);
      if (note) box.append(note);
      return;
    }
    const pts = [...pos, ...others.slice(-2000)];
    const vals = pts.map(S);
    const vmin = Math.min(...vals), vmax = Math.max(...vals);
    const log = vmax / vmin > 8;
    let y, yticks;
    if (log) {
      const a = Math.max(-300, Math.floor(Math.log10(vmin))), b = Math.min(300, Math.max(a + 1, Math.ceil(Math.log10(vmax))));
      const lo = 10 ** a, hi = 10 ** b;
      y = v => m.t + (Math.log10(hi) - Math.log10(Math.min(hi, Math.max(v, lo)))) / (Math.log10(hi) - Math.log10(lo)) * (H - m.t - m.b);
      yticks = [];
      const every = Math.max(1, Math.ceil((b - a) / 6));
      for (let k = a; k <= b; k += every) for (const f of (b - a > 3 ? [1] : [1, 2, 5])) { const v = f * 10 ** k; if (v >= lo && v <= hi) yticks.push(v); }
    } else {
      const step = niceStep(vmax, 4), hi = Math.ceil(vmax * 1.08 / step) * step;
      y = v => m.t + (1 - v / hi) * (H - m.t - m.b);
      yticks = [];
      for (let v = 0; v <= hi + 1e-9; v += step) yticks.push(v);
    }
    m.l = Math.max(m.l, 14 + 7 * Math.max(...yticks.map(v => tickText(v, u).length)));   // the widest tick fits
    const t = e => evaluatedAt(e).getTime();
    const end = Math.max(...pts.map(t), data.updated ? data.updated.getTime() : 0);
    let t0 = Math.min(...pts.map(t)), t1 = end;
    if (t1 - t0 < 86400e3) { t0 -= 86400e3; t1 += 86400e3; }
    const padT = (t1 - t0) * 0.04;
    t0 -= padT; t1 += padT;
    const x = v => m.l + (v - t0) / (t1 - t0) * (W - m.l - m.r);
    for (const v of yticks) {
      s.append(svg('line', { class: 'grid', x1: m.l, x2: W - m.r, y1: y(v), y2: y(v) }));
      s.append(svg('text', { class: 'tick', x: m.l - 8, y: y(v) + 4, 'text-anchor': 'end' }, tickText(v, u)));
    }
    s.append(svg('line', { class: 'axis', x1: m.l, x2: W - m.r, y1: H - m.b, y2: H - m.b }));
    const days = (t1 - t0) / 86400e3;
    const nT = Math.max(2, Math.floor((W - m.l - m.r) / 110));
    const dayStep = [1, 2, 7, 14, 30, 61, 91, 182, 365].find(d => days / d <= nT) || Math.ceil(days / nT);
    const first = new Date(t0); first.setUTCHours(0, 0, 0, 0);
    for (let d = first.getTime() + 86400e3; d <= t1; d += dayStep * 86400e3) {
      if (d < t0) continue;
      const lbl = new Date(d).toLocaleDateString('en-US', { month: 'short', day: 'numeric', timeZone: 'UTC' });
      s.append(svg('text', { class: 'tick', x: x(d), y: H - m.b + 18, 'text-anchor': 'middle' }, lbl));
    }
    // the record line: each record holds until the next one at the same pin; a new pin breaks it
    let d = '', prev = null;
    for (const e of pos) {
      const px = x(t(e)).toFixed(1), py = y(S(e)).toFixed(1);
      d += prev && prev.harness_commit === e.harness_commit ? `H${px}V${py}` : `M${px} ${py}`;
      prev = e;
    }
    s.append(svg('path', { class: 'step', d }));
    const cur = data.record[tr.id] && pos.includes(data.record[tr.id]) ? data.record[tr.id] : null;
    if (cur) s.append(svg('path', { class: 'step-tail', d: `M${x(t(cur)).toFixed(1)} ${y(S(cur)).toFixed(1)}H${x(end).toFixed(1)}` }));
    const word = e => e.record_in.includes(tr.id) ? (retiredIn(e, tr.id) ? 'retired record' : 'record') : 'accepted';
    const showTip = (e, px, py) => {
      tip.replaceChildren(el('strong', null, nm(e)), `${tr.sym} = ${fmtS(S(e), u)} ${u}`, el('br'),
        fmtDate(evaluatedAt(e)) + ', ' + word(e) + (e.author ? ', ' + e.author : ''));
      tip.hidden = false;
      const bw = box.clientWidth;
      tip.style.left = Math.max(8, Math.min(px + 14, bw - 268)) + 'px';
      tip.style.top = Math.max(4, py - 64) + 'px';
    };
    const hide = () => { tip.hidden = true; };
    const point = (e, cls, r) => {
      const px = x(t(e)), py = y(S(e));
      const a = svg('a', { href: page('submission.html', { id: e.id }), 'aria-label': `${nm(e)}: ${tr.sym} ${fmtS(S(e), u)} ${u}, ${fmtDate(evaluatedAt(e))}, ${word(e)}` },
        svg('circle', { class: 'hit', cx: px, cy: py, r: 12 }),
        svg('circle', { class: cls, cx: px, cy: py, r }));
      const scale = () => s.getBoundingClientRect().width / W;
      a.addEventListener('pointerenter', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('focus', () => showTip(e, px * scale() + 8, py * scale() + 8));
      a.addEventListener('pointerleave', hide);
      a.addEventListener('blur', hide);
      s.append(a);
    };
    for (const e of others.slice(-2000)) point(e, 'pt-other', 3.6);
    for (const e of pos) point(e, retiredIn(e, tr.id) ? 'pt-retired' : 'pt-record', 5);
    const lab = cur || pos[pos.length - 1];
    s.append(svg('text', { class: 'direct', x: x(t(lab)) + 9, y: y(S(lab)) - 9 }, fmtS(S(lab), u) + ' ' + u));
    box.append(s);
    const hasRetired = pos.some(e => retiredIn(e, tr.id));
    if (others.length || hasRetired) box.append(el('div', { class: 'legend' }, el('span', { class: 'lg-record' }, 'Record'),
      hasRetired ? el('span', { class: 'lg-retired' }, 'Retired record') : null,
      others.length ? el('span', { class: 'lg-other' }, 'Accepted, not a record of this track') : null));
    if (log) box.append(el('div', { class: 'legend' }, el('span', { class: 'muted' }, 'Logarithmic scale.')));
    if (note) box.append(note);
    box.append(tip);
  }

  // ---- leaderboard: every record of the track, newest first, grouped by contract pin ------------
  function leaderboard(recs, tr, data, nm) {
    document.getElementById('leaderboard-note').textContent =
      `Every ${tr.label.toLowerCase()} record, newest first. A new record needs a score ${tr.sym} more than ${marginText(data)} below the standing record's, at the same contract pin. Gain: 1 \u2212 ${tr.sym} / ${tr.sym},record against the record it beat.`;
    document.getElementById('leaders-caption').textContent = `Every ${tr.label.toLowerCase()} record, newest first, grouped by contract pin`;
    const cols = 8;
    const th = (label, cls, title) => el('th', { scope: 'col', class: cls || null, title: title || null }, label);
    // the columns: P_total and the priced proof's size, each row's own (`pricedBy`: this track's
    // proof, or the final proof for rows of the first v6 rules; a board of both kinds names the
    // priced proof per cell); the score's unit in the header when every row has the same one
    const defs = [...new Set(recs.map(e => window.RF.pricedBy(tr, window.RF.partsIn(e.score, tr.id))))];
    const hd = defs.length === 1 ? defs[0] : tr, mixed = new Set(defs.map(d => d.size[0])).size > 1;
    const units = new Set(defs.map(d => d.unit)), oneUnit = units.size === 1 ? hd.unit : null;
    document.getElementById('leaders-head').replaceChildren(el('tr', null,
      th('#', 'num'), th('Entry'), th('Author'), th([hd.sym, oneUnit ? [' (', window.RF.unitNode(oneUnit), ')'] : null], 'num',
        'the score of this track, ' + (oneUnit ? oneUnit : 'in each row\'s unit')),
      th('P_total (s)', 'num', 'the median of three timed passes\' totals'),
      th(mixed ? 'priced |\u03c0|' : hd.size[1], 'num', mixed ? 'the proof the row\'s score prices' : 'the priced proof\'s size'),
      th('Gain', 'num'), th('Date')));
    const tb = document.getElementById('leaders');
    tb.replaceChildren();
    if (!recs.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: cols }, `No ${tr.label.toLowerCase()} records yet. The first certified, comparable, attested ACCEPT whose confirmation run is one too takes the board.`)));
      return;
    }
    const numbered = recs.map((e, i) => ({ e, n: i + 1 })).reverse();
    let pin;
    for (const { e, n } of numbered) {
      if (e.harness_commit !== pin) {
        pin = e.harness_commit;
        tb.append(el('tr', { class: 'pin-row' }, el('th', { colspan: cols },
          'Contract pin ', pin ? ext(link.core(pin), short(pin)) : 'unknown',
          pin && pin === data.core ? ' (current)' : ' (earlier pin)')));
      }
      const sc = window.RF.partsIn(e.score, tr.id), rowDef = window.RF.pricedBy(tr, sc);
      const gain = gainOf(e, tr.id);
      const a = e.against[tr.id];
      const isCur = data.record[tr.id] && data.record[tr.id].id === e.id;
      tb.append(el('tr', { class: isCur ? 'current' : null },
        el('td', { class: 'num' }, String(n)),
        el('td', null, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
          isCur ? [' ', el('span', { class: 'badge st-record' }, 'current')] : retiredIn(e, tr.id) ? [' ', badge('retired')] : null),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', { class: 'num' }, el('strong', null, fmtS(scoreIn(e, tr.id), unitOf(e, tr))), oneUnit ? null : [' ', el('small', null, window.RF.unitNode(unitOf(e, tr)))]),
        el('td', { class: 'num' }, fmtPart(sc.P_total_s, 's')),
        el('td', { class: 'num', title: mixed ? rowDef.size[1] : null }, fmtPart(sc[rowDef.size[0]], rowDef.old ? 'bytes' : 'B')),
        el('td', { class: 'num' + (gain !== null && e.record_of[tr.id] ? ' gain' : ''), title: gain !== null && a.S_record !== null ? `Against the ${fmtS(a.S_record, unitOf(e, tr))} ${unitOf(e, tr)} of the record it beat` : null },
          gain !== null && e.record_of[tr.id] ? pct(gain) : e.port_of ? 'ported' : 'first at pin'),
        el('td', null, timeEl(evaluatedAt(e)))));
    }
  }

  // ---- queue: running first, then a waiting port, then the bot's fair order by author ------------
  function queueOrder(subs) {
    const running = subs.filter(e => e.status === 'running').sort((a, b) => (a.started || 0) - (b.started || 0));
    // a waiting port of the record to a new pin, or a record candidate's confirmation run, first,
    // oldest first (the bot's order)
    const first = e => !!(e.port_of || e.confirming);
    const front = subs.filter(e => e.status === 'queued' && first(e)).sort((a, b) => (a.queued || 0) - (b.queued || 0));
    const queued = subs.filter(e => e.status === 'queued' && !first(e)).sort((a, b) => (a.queued || 0) - (b.queued || 0));
    const lastStart = new Map();
    for (const e of subs) { const t = countedStart(e); if (e.author && t) lastStart.set(e.author, Math.max(lastStart.get(e.author) || -Infinity, t.getTime())); }
    const order = front.slice();
    let clock = Date.now() + 1;
    const byAuthor = new Map();
    for (const e of queued) { if (!byAuthor.has(e.author)) byAuthor.set(e.author, []); byAuthor.get(e.author).push(e); }
    while (byAuthor.size && order.length < 500 + front.length) {
      let best = null;
      for (const [a, list] of byAuthor) {
        const ls = lastStart.has(a) ? lastStart.get(a) : -Infinity, e = list[0];
        if (!best || ls < best.ls || (ls === best.ls && (e.queued || 0) < (best.e.queued || 0))) best = { a, e, ls };
      }
      order.push(best.e);
      const list = byAuthor.get(best.a); list.shift();
      if (!list.length) byAuthor.delete(best.a);
      lastStart.set(best.a, clock++);
    }
    return { running, order, total: queued.length + front.length };
  }
  // the fair order's start of an author's evaluation (AGENTS.md §9), as the bot's
  // rfqueue.counted_start: `counted_at`, the start of its first run that counted (none after a named
  // organiser error, nor after an entry's first unnamed ERROR or first run with no result at all);
  // superseded and withdrawn entries never count. There is no cap on an author's evaluations.
  function countedStart(e) {
    if (e.port_of || ['superseded', 'withdrawn', 'invalid'].includes(e.status)) return null;
    if (e.status === 'running') return e.counted_at || e.started || null;
    if (e.has_counted) return e.counted_at || null;
    return e.started && e.verdict !== 'ERROR' ? e.started : null;
  }
  function queue(subs, nm) {
    const ol = document.getElementById('queue');
    const { running, order, total } = queueOrder(subs);
    ol.replaceChildren();
    document.getElementById('queue-count').textContent = running.length + total ? `${running.length} running, ${total} queued` : '';
    if (!running.length && !order.length) {
      ol.append(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, 'The queue is empty. A pull request that changes one submissions/<root>/ is queued as soon as it is opened.')));
      return;
    }
    const item = (e, pos) => el('li', null,
      el('span', { class: 'pos' }, pos),
      el('span', null, badge(e.status), ' ', el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
        ' ', el('span', { class: 'muted' }, 'by '), e.author ? ext(link.author(e), e.author) : '–',
        ' ', el('span', { class: 'muted' }, '('), ext(link.pr(e), '#' + e.pr), el('span', { class: 'muted' }, ')'),
        e.confirming ? [' ', el('span', { class: 'muted' }, 'record candidate: confirmation run')] : null),
      el('span', { class: 'when' }, e.status === 'running' ? (e.started ? 'started ' + ago(e.started) : 'started')
        : (e.queued ? 'queued ' + ago(e.queued) : 'queued')));
    running.forEach(e => ol.append(item(e, '▸')));
    order.forEach((e, i) => ol.append(item(e, String(i + 1))));
    if (total > order.length) ol.append(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, `and ${total - order.length} more`)));
  }

  // ---- all submissions --------------------------------------------------------------------------
  const PAGE = 200;
  const state = { status: 'all', q: '', limit: PAGE };
  function submissions(data, nm, focusKey) {
    const rel = window.RF.relations(data.subs);
    const sorted = data.subs.slice().sort((a, b) => ((b.queued || b.opened || 0) - (a.queued || a.opened || 0)) || b.pr - a.pr);
    const counts = new Map();
    for (const e of sorted) counts.set(e.status, (counts.get(e.status) || 0) + 1);
    const chips = document.getElementById('chips');
    chips.replaceChildren();
    const chip = (key, label, n) => {
      const b = el('button', { type: 'button', class: 'chip', 'data-key': key, 'aria-pressed': String(state.status === key) }, `${label} ${n}`);
      b.addEventListener('click', () => { state.status = key; state.limit = PAGE; submissions(data, nm, key); });
      chips.append(b);
    };
    chip('all', 'All', sorted.length);
    for (const st of window.RF.STATUSES) if (counts.get(st)) chip(st, st, counts.get(st));
    if (focusKey) { const f = chips.querySelector(`button[data-key="${focusKey}"]`); if (f) f.focus(); }
    const q = state.q.toLowerCase();
    const rows = sorted.filter(e => (state.status === 'all' || e.status === state.status) &&
      (!q || [e.root, e.author, e.agent, e.title, e.id, '#' + e.pr].some(v => v && v.toLowerCase().includes(q))));
    const tb = document.getElementById('subs');
    tb.replaceChildren();
    if (!sorted.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, 'No submissions yet. Open the first pull request and it is evaluated next.')));
    } else if (!rows.length) {
      tb.append(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, 'Nothing matches this filter.')));
    }
    for (const e of rows.slice(0, state.limit)) {
      const n = rel.citeCount(e.pr);
      const credit = [];
      if (n) credit.push(el('span', { title: 'Pull requests by other authors, with a verdict, that say they build on this one' }, 'cited by ' + n));
      if (e.builds_on.length) credit.push(el('span', { class: 'muted' }, (credit.length ? ', ' : '') + 'builds on ' + e.builds_on.map(k => '#' + k).join(' ')));
      tb.append(el('tr', null,
        el('td', null, badge(e.status), unverified(e) ? [' ', unverified(e)] : null),
        el('td', { class: 'wrap-ok' }, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
          e.title ? el('span', { class: 'sub' }, e.title) : null),
        el('td', { class: 'num' }, ext(link.pr(e), '#' + e.pr)),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, el('span', { class: 'agent' }, e.agent || '–')),
        // (an earlier season's score, in another unit than the header's, carries its own)
        window.RF.TRACK_IDS.map(t => el('td', { class: 'num' }, scoreIn(e, t) !== null ? fmtS(scoreIn(e, t), unitOf(e, trackOf(t))) : '–',
          scoreIn(e, t) !== null && unitOf(e, trackOf(t)) !== trackOf(t).unit ? [' ', el('small', null, unitOf(e, trackOf(t)))] : null,
          e.record_in.includes(t) ? el('span', { class: 'rec-mark', title: retiredIn(e, t) ? 'took this track\'s record (retired since)' : 'took this track\'s record' }, retiredIn(e, t) ? ' \u2020' : ' \u2605') : null)),
        el('td', null, timeEl(e.finished || e.queued || e.opened)),
        el('td', null, credit.length ? credit : '–')));
    }
    const more = document.getElementById('subs-more');
    more.replaceChildren();
    if (rows.length > state.limit) {
      const b = el('button', { type: 'button', class: 'button ghost' }, `Show ${Math.min(PAGE, rows.length - state.limit)} more`);
      b.addEventListener('click', () => { state.limit += PAGE; submissions(data, nm); });
      more.append(b);
    }
    const notes = [];
    if (data.skipped) notes.push(`${data.skipped} malformed entries were skipped.`);
    if (data.notShown) notes.push(`${data.notShown} older entries beyond the site's 20,000 are not shown.`);
    document.getElementById('subs-count').textContent = sorted.length
      ? `Showing ${Math.min(rows.length, state.limit)} of ${rows.length}` + (rows.length !== sorted.length ? ` matching (${sorted.length} in all)` : '') + '. '
        + (rows.length > state.limit ? 'Refine the search or show more. ' : '') + notes.join(' ') : '';
  }

  // ---- a paused queue: the bot stopped evaluating after repeated organiser errors ---------------
  function pausedBanner(data) {
    const box = document.getElementById('paused');
    if (!data.paused) { box.hidden = true; box.replaceChildren(); return; }
    const { el, timeEl } = window.RF;
    box.replaceChildren(el('strong', null, 'Evaluations are paused'),
      ...(data.paused.since ? [' since ', timeEl(data.paused.since, true)] : []),
      ': several recent runs failed on the organiser\u2019s side, and the owner has been notified. '
      + 'Queued entries keep their places, and nothing is charged to their authors.');
    box.hidden = false;
  }

  // ---- failure ----------------------------------------------------------------------------------
  function failed(err) {
    const box = document.getElementById('record');
    const host = (() => { try { return new URL(window.RF.BASE, location.href).host; } catch (e) { return 'the data branch'; } })();
    const retry = el('button', { type: 'button', class: 'button' }, 'Try again');
    retry.addEventListener('click', () => { box.replaceChildren(el('p', { class: 'loading' }, 'Loading results…')); start(true); });
    box.replaceChildren(el('div', { class: 'notice', role: 'alert' },
      el('h2', null, 'The results did not load'),
      el('p', null, `Could not read submissions.json from ${host}: ${err && err.message ? err.message : 'unknown error'}. Check your connection and try again; the data is also on the `,
        ext(link.repo + '/tree/data', 'data branch'), '.'), retry));
    const msg = 'Results unavailable.';
    document.getElementById('leaders').replaceChildren(el('tr', { class: 'empty-row' }, el('td', { colspan: 8 }, msg)));
    document.getElementById('subs').replaceChildren(el('tr', { class: 'empty-row' }, el('td', { colspan: 9 }, msg)));
    document.getElementById('queue').replaceChildren(el('li', { class: 'empty-li' }, el('span', { class: 'empty' }, msg)));
    document.getElementById('chart').replaceChildren();
    document.getElementById('chips').replaceChildren();
    window.RF.footer(null);
  }

  let current = null, names = null;
  // the three sections of the selected track
  function renderTrack(data) {
    const { section } = window.RF;
    const tr = trackOf(track);
    const nm = names || (e => e.root || e.id);
    let recs = [];
    section('records', 'record', () => { recs = window.RF.records(data.subs, tr.id); });
    section('current record', 'record', () => recordCard(recs, tr, data, nm));
    section('progression', 'chart', () => chart(recs, tr, data, nm));
    section('leaderboard', 'leaders', () => leaderboard(recs, tr, data, nm));
  }
  async function start(force) {
    let data;
    try { data = await window.RF.loadData(force); } catch (err) { failed(err); return; }
    current = data;
    const { section } = window.RF;
    section('names', 'record', () => { names = window.RF.nameOf(data.subs); });
    const nm = names || (e => e.root || e.id);
    section('pause', 'paused', () => pausedBanner(data));
    renderTrack(data);
    section('queue', 'queue', () => queue(data.subs, nm));
    section('submissions', 'subs', () => submissions(data, nm));
    section('footer', 'pin', () => window.RF.footer(data));
  }

  document.addEventListener('DOMContentLoaded', () => {
    tabs(() => { if (current) renderTrack(current); });
    const q = document.getElementById('q');
    let timer = 0;
    q.addEventListener('input', () => {
      clearTimeout(timer);
      timer = setTimeout(() => { state.q = q.value.trim(); state.limit = PAGE; if (current) window.RF.section('submissions', 'subs', () => submissions(current, names || (e => e.root || e.id))); }, 150);
    });
    let w = 0;
    new ResizeObserver(entries => {
      const nw = Math.round(entries[0].contentRect.width);
      if (current && Math.abs(nw - w) > 4) {
        w = nw;
        const tr = trackOf(track);
        window.RF.section('progression', 'chart', () => chart(window.RF.records(current.subs, tr.id), tr, current, names || (e => e.root || e.id)));
      } else w = nw;
    }).observe(document.getElementById('chart'));
    start(false);
  });
})();
