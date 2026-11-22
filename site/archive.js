// recursion.fast: the archive page. Every entry of an archived season (the bot's `season`, derived
// from the attested pin it was evaluated at), grouped by season, newest first, with that season's
// scores, verdicts and records. Nothing here is ranked against the current season.
'use strict';
(function () {
  const { el, ext, page, link, fmtS, timeEl, badge, evaluatedAt, unverified, shortSha, section, productRule, UNIT } = window.RF;

  // a score as its season named it: each field once, with the tracks it scored (`tracks`, or the
  // sum's `S` alone for a score without them)
  function scoreText(sc) {
    if (!sc) return '–';
    const names = sc.tracks || { sum: 'S' }, out = [];
    for (const [t, f] of Object.entries(names)) {
      if (typeof sc[f] !== 'number') continue;
      const g = out.find(x => x[0] === f);
      if (g) g[2].push(t); else out.push([f, sc[f], [t]]);
    }
    const u = productRule(sc) ? UNIT : 's';                 // that season's unit
    return out.length ? out.map(([f, v, ts]) => `${f} = ${fmtS(v, u)} ${u} (${ts.join(', ')})`).join('; ') : '–';
  }

  function season(sn, es, nm) {
    const box = el('section', { class: 'archive-season', id: sn.id, 'aria-labelledby': 'h-' + sn.id });
    const tracks = sn.tracks.length ? sn.tracks : [...new Set(es.flatMap(e => e.record_in))];
    // the season's last record in each of its tracks (the newest entry that took it)
    const last = tracks.map(t => [t, es.filter(e => e.record_in.includes(t)).sort((a, b) => (evaluatedAt(b) || 0) - (evaluatedAt(a) || 0))[0]])
      .filter(([, e]) => e);
    box.append(el('h2', { id: 'h-' + sn.id }, sn.id, ': ', sn.title),
      el('p', { class: 'muted' },
        sn.pins.length ? ['Contract pins ', sn.pins.flatMap((p, i) => [i ? ', ' : '', ext(link.core(p), shortSha(p))]), '. '] : null,
        sn.dir ? ['Record roots: ', ext(link.mainDir(sn.dir), sn.dir + '/'), ' on main. '] : null,
        `${es.length} ${es.length === 1 ? 'entry' : 'entries'}.`),
      last.length ? el('p', null, 'Its last records: ', last.flatMap(([t, e], i) => [i ? '; ' : '', el('strong', null, t), ' ',
        el('a', { href: page('submission.html', { id: e.id }) }, nm(e)), ` (${scoreText(e.score)})`]), '.') : null);
    const tb = el('tbody');
    for (const e of es.slice().sort((a, b) => (evaluatedAt(b) || 0) - (evaluatedAt(a) || 0) || b.pr - a.pr)) {
      tb.append(el('tr', null,
        el('td', null, badge(e.status), unverified(e) ? [' ', unverified(e)] : null),
        el('td', { class: 'wrap-ok' }, el('a', { class: 'entry', href: page('submission.html', { id: e.id }) }, nm(e)),
          e.title ? el('span', { class: 'sub' }, e.title) : null),
        el('td', { class: 'num' }, ext(link.pr(e), '#' + e.pr)),
        el('td', null, e.author ? ext(link.author(e), e.author) : '–'),
        el('td', null, e.verdict || '–'),
        el('td', null, scoreText(e.score)),
        el('td', null, e.record_in.length ? e.record_in.join(', ') : '–'),
        el('td', null, timeEl(evaluatedAt(e)))));
    }
    const th = label => el('th', { scope: 'col' }, label);
    box.append(el('div', { class: 'table-wrap', role: 'region', tabindex: '0', 'aria-labelledby': 'h-' + sn.id },
      el('table', { class: 'data' },
        el('caption', { class: 'visually-hidden' }, `Every entry of ${sn.id}, newest first`),
        el('thead', null, el('tr', null, th('Status'), th('Entry'), th('PR'), th('Author'), th('Verdict'),
          th(`Score (${sn.id} rules)`), th('Record of'), th('Date'))),
        tb)));
    return box;
  }

  async function start() {
    const box = document.getElementById('seasons');
    let data;
    try { data = await window.RF.loadData(); } catch (err) {
      box.replaceChildren(el('p', { class: 'notice', role: 'alert' }, 'The archive did not load: ' + (err && err.message ? err.message : 'unknown error') + '.'));
      window.RF.footer(null);
      return;
    }
    section('archive', 'seasons', () => {
      const nm = window.RF.nameOf(data.all);
      const by = new Map(data.seasons.map(s => [s.id, []]));
      for (const e of data.archived) { if (!by.has(e.season)) by.set(e.season, []); by.get(e.season).push(e); }
      // the newest season first (the bot lists them oldest first)
      const order = data.seasons.slice().reverse();
      box.replaceChildren(...(order.length ? order.map(sn => season(sn, by.get(sn.id) || [], nm))
        : [el('p', { class: 'muted' }, 'No season has been archived yet.')]));
    });
    section('footer', 'pin', () => window.RF.footer(data));
  }
  document.addEventListener('DOMContentLoaded', () => start());
})();
