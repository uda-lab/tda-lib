// Only bundled TeX packages: never autoload extensions or send content to a CDN.
window.MathJax = {
  options: { enableMenu: false },
  tex: {
    packages: ['base', 'ams', 'newcommand', 'noundefined'],
    inlineMath: [['\\(', '\\)']],
    displayMath: [['\\[', '\\]']]
  },
  svg: { fontCache: 'local' }
};
