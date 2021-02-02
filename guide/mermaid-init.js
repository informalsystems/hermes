// Adapt Mermaid theme to rustdoc theme.
// https://github.com/mersinvald/aquamarine/blob/ce24cd6e3a84e4f80a60c21e218b9c6f26b001fa/src/attrs.rs#L89-L101

function get_mermaid_theme() {
  let is_dark = /.*(dark|coal|navy|ayu).*/.test(document.documentElement.className);
  if (is_dark) {
    return 'dark';
  } else {
    return 'default';
  }
}

mermaid.initialize({
  startOnLoad: true,
  theme: get_mermaid_theme()
});
