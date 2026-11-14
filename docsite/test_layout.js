/* Read-only browser regression probe. After building and serving the preview,
   open /tda-lib/docs/api/ at 320, 390 and 1280 CSS px, wait for equations/fonts,
   and evaluate this expression in the browser. It throws on a failed contract.
   This probe is not included in the published source inventory. */
(() => {
  const require = (condition, message) => {
    if (!condition) throw new Error(message);
  };
  const root = document.documentElement;
  const article = document.querySelector('[itemprop="articleBody"]');
  require(article, 'Open a rendered curated documentation page');
  require(root.scrollWidth <= root.clientWidth + 1,
    `Page overflows: ${root.scrollWidth}px at ${root.clientWidth}px viewport`);

  const tables = [...article.querySelectorAll('table')];
  const formulas = [...article.querySelectorAll('div.arithmatex')];
  require(tables.length > 0 && formulas.length > 0,
    'Use the API/import guide, which exercises tables and display equations');
  for (const table of tables) {
    const scrolls = table.scrollWidth > table.clientWidth + 1;
    require(!scrolls || getComputedStyle(table).overflowX === 'auto',
      'Wide tables need their own horizontal scroller');
    require(table.getBoundingClientRect().width <= article.clientWidth + 1,
      'Table is wider than the article');
    for (const cell of table.querySelectorAll('th, td')) {
      if (scrolls) {
        const maximum = +getComputedStyle(cell).maxWidth.replace("px", "");
        require(maximum > 0 && cell.getBoundingClientRect().width <= maximum + 1,
          'Scrolling table columns must have a bounded readable width');
      }
      require(getComputedStyle(cell).whiteSpace === 'normal', 'Table cells must wrap');
      require(getComputedStyle(cell).overflowWrap === 'anywhere',
        'Long table identifiers must wrap');
    }
  }
  for (const formula of formulas) {
    const container = formula.querySelector('mjx-container[jax="SVG"]');
    const svg = container?.querySelector('svg');
    require(svg, 'Wait for every display equation to be typeset');
    require(!formula.querySelector('[data-mml-node="merror"], mjx-merror'),
      'MathJax reported an equation error');
    require(getComputedStyle(formula).overflowX === 'auto',
      'Wide display equations need their own horizontal scroller');
    require(formula.getBoundingClientRect().width <= article.clientWidth + 1,
      'Equation wrapper is wider than the article');
    require(svg.getBoundingClientRect().left + formula.scrollLeft >= formula.getBoundingClientRect().left - 1,
      'Centered equation starts outside the reachable scroll area');
    require(formula.scrollWidth + 1 >= svg.getBoundingClientRect().width,
      'The equation scroller clips the right edge');
  }
  return {
    viewport: root.clientWidth,
    pageWidth: root.scrollWidth,
    tables: tables.length,
    scrollableTables: tables.filter(e => e.scrollWidth > e.clientWidth + 1).length,
    displayEquations: formulas.length,
    scrollableEquations: formulas.filter(e => e.scrollWidth > e.clientWidth + 1).length,
  };
})()
