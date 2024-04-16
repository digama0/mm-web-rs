use crate::{Extra, THMS_PER_PAGE};
use itertools::Itertools;
use metamath_rs::{
  comment_parser::{CommentItem, CommentParser, Date, Parenthetical},
  nameck::{Atom, NameReader, Nameset},
  parser::HeadingLevel,
  proof::ProofTreeArray,
  scopeck::{Frame, Hyp, VerifyExpr},
  statement::StatementAddress,
  *,
};
use std::{
  collections::{BTreeSet, BinaryHeap, HashMap, HashSet},
  fmt::Display,
  io::{self, Write},
  ops::Bound,
  sync::Mutex,
};

const GREEN_TITLE_COLOR: &str = "#006633";
const GRAY_BORDER_COLOR: &str = "#B2B2B2";
const MINT_BACKGROUND_COLOR: &str = "#EEFFFA";
const PURPLISH_BIBLIO_COLOR: &str = "#FAEEFF";
const SANDBOX_COLOR: &str = "#FFFFD9";

#[derive(Clone, Copy)]
struct Heading<'a> {
  header: &'a str,
  content: &'a str,
  level: HeadingLevel,
  stmt_num: usize,
  index: [u16; 4],
}

impl<'a> Heading<'a> {
  fn idx(&self) -> impl Display {
    let [i1, i2, i3, i4] = self.index;
    let level = self.level;
    DisplayFn(move |f| match level {
      HeadingLevel::MajorPart => write!(f, "{i1}"),
      HeadingLevel::Section => write!(f, "{i1}.{i2}"),
      HeadingLevel::SubSection => write!(f, "{i1}.{i2}.{i3}"),
      HeadingLevel::SubSubSection => write!(f, "{i1}.{i2}.{i3}.{i4}"),
      HeadingLevel::Database | HeadingLevel::Statement => unreachable!(),
    })
  }

  fn header(&self) -> impl Display + 'a {
    let idx = self.idx();
    let header = self.header;
    let level = self.level;
    DisplayFn(move |f| {
      write!(
        f,
        "{}{idx}&nbsp;&nbsp;{header}",
        if level == HeadingLevel::MajorPart { "PART " } else { "" }
      )
    })
  }
}

pub(crate) struct Renderer<'a> {
  pub(crate) db: &'a Database,
  pink_numbers: HashMap<&'a [u8], usize>,
  mathbox_addr: Option<StatementAddress>,
  mathbox_lookup: Option<Vec<(StatementAddress, &'a str)>>,
  // latex_defs: HashMap<&'a [u8], &'a str>,
  html_defs: HashMap<&'a [u8], &'a str>,
  alt_html_defs: HashMap<&'a [u8], &'a str>,
  html_var_color: String,
  html_title: &'a str,
  html_title_abbr: String,
  html_home: &'a str,
  html_home_href: &'a str,
  html_home_img: &'a str,
  html_dir: &'a str,
  alt_html_dir: &'a str,
  html_bibliography: &'a str,
  html_css: String,
  html_font: &'a str,
  ext_html_addr: Option<StatementAddress>,
  ext_html_title: &'a str,
  ext_html_title_abbr: String,
  ext_html_home_href: &'a str,
  ext_html_home_img: &'a str,
  ext_html_bibliography: &'a str,
  html_ext_url: &'a str,
  first_order_tc: Vec<Atom>,
  second_order_tc: Vec<Atom>,
  syntax_hint: HashMap<&'a [u8], Box<[u8]>>,
  trace_usage: Mutex<TraceUsage<'a>>,
  used_by: Option<HashMap<&'a [u8], Vec<StatementAddress>>>,
  syntax_used: Option<Vec<Box<[Atom]>>>,
  pub(crate) statements: Vec<StatementRef<'a>>,
  headings: Vec<Heading<'a>>,
  pub(crate) recent: Vec<(Date, usize)>,
  recent_templates: Vec<Template<'a>>,
}

impl<'a> Renderer<'a> {
  pub(crate) fn new(db: &'a Database) -> Self {
    let pink_numbers = db
      .statements()
      .filter(|s| s.is_assertion())
      .enumerate()
      .map(|(i, l)| (l.label(), i))
      .collect();
    let ts = &**db.typesetting_result();
    let html_title = ts.html_title.as_ref().map_or("Metamath Test Page", |s| as_str(&s.1));
    let html_home = ts.html_home.as_ref().map_or(
      // note: "HREF=" and "IMG SRC=" must be all caps, see #2
      "<a HREF=\"mmset.html\">\
        <IMG SRC=\"mm.gif\" alt=\"Home\" height=32 width=32 \
          style=\"vertical-align: middle; margin-bottom: 0\">Home\
      </a>",
      |s| as_str(&s.1),
    );
    let names = db.name_result();
    let get_tc = |arr: &[&[u8]]| arr.iter().map(|v| names.lookup_symbol(v).unwrap().atom).collect();
    let mathbox_addr = names.lookup_label(b"mathbox").map(|l| l.address);
    let ext_html_title = ts.ext_html_title.as_ref().map_or("", |s| as_str(&s.1));
    let ext_html_home = ts.ext_html_home.as_ref().map(|s| as_str(&s.1));
    let ext_html_home_href = ext_html_home
      .and_then(|s| Some(s.split_once("HREF=\"")?.1.split_once('\"')?.0))
      .unwrap_or_default();
    let ext_html_home_img = ext_html_home
      .and_then(|s| Some(s.split_once("IMG SRC=\"")?.1.split_once('\"')?.0))
      .unwrap_or_default();
    Self {
      db,
      pink_numbers,
      mathbox_addr,
      mathbox_lookup: None,
      // latex_defs: ts.latex_defs.iter().map(|(x, y)| (&**x, as_str(y))).collect(),
      html_defs: ts.html_defs.iter().map(|(x, y)| (&**x, as_str(&y.2))).collect(),
      alt_html_defs: ts.alt_html_defs.iter().map(|(x, y)| (&**x, as_str(&y.2))).collect(),
      html_var_color: Itertools::intersperse(ts.html_var_color.iter().map(|s| as_str(&s.1)), " ")
        .collect::<String>(),
      html_title,
      html_title_abbr: format!(
        "{abbr} Home",
        abbr = html_title.matches(|c: char| c.is_ascii_uppercase()).collect::<String>()
      ),
      html_dir: ts.html_dir.as_ref().map_or("", |s| as_str(&s.1)),
      alt_html_dir: ts.alt_html_dir.as_ref().map_or("", |s| as_str(&s.1)),
      html_bibliography: ts.html_bibliography.as_ref().map_or("", |s| as_str(&s.1)),
      html_css: ts
        .html_css
        .as_ref()
        .map_or("", |s| as_str(&s.1))
        .replace("\\n", "\n")
        .replace("STYLE TYPE=\"text/css\"", "style"),
      html_font: ts.html_font.as_ref().map_or("", |s| as_str(&s.1)),
      ext_html_addr: ts
        .ext_html_label
        .as_ref()
        .and_then(|s| names.lookup_label(&s.1))
        .map(|l| l.address),
      ext_html_title,
      ext_html_title_abbr: format!(
        "{abbr} Home",
        abbr = ext_html_title.matches(|c: char| c.is_ascii_uppercase()).collect::<String>()
      ),
      ext_html_home_href,
      ext_html_home_img,
      ext_html_bibliography: ts.ext_html_bibliography.as_ref().map_or("", |s| as_str(&s.1)),
      html_ext_url: ts.html_ext_url.as_ref().map_or("", |s| as_str(&s.1)),
      html_home,
      html_home_href: html_home.split_once("HREF=\"").unwrap().1.split_once('\"').unwrap().0,
      html_home_img: html_home.split_once("IMG SRC=\"").unwrap().1.split_once('\"').unwrap().0,
      first_order_tc: get_tc(&[b"setvar"]),
      second_order_tc: get_tc(&[b"wff", b"class"]),
      syntax_hint: db
        .statements()
        .filter(|stmt| stmt.statement_type() == StatementType::Axiom && *stmt.math_at(0) != *b"|-")
        .filter_map(|stmt| {
          let fr = db.scope_result().get(stmt.label())?;
          let e = &fr.target;
          let mut iter = TokenIter::new();
          for sp in e.tail.iter().map(|frag| &frag.prefix).chain([&e.rump]) {
            iter.pool = &fr.const_pool[sp.clone()];
            while let Some(tk) = iter.next() {
              if !matches!(tk, b"(" | b")" | b":" | b",") {
                return Some((stmt.label(), tk.into()))
              }
            }
          }
          None
        })
        .collect(),
      trace_usage: Default::default(),
      used_by: None,
      syntax_used: None,
      statements: vec![],
      headings: Default::default(),
      recent: vec![],
      recent_templates: vec![],
    }
  }

  pub(crate) fn num_pages(&self) -> usize {
    (self.statements.len() + (THMS_PER_PAGE - 1)) / THMS_PER_PAGE
  }
  pub(crate) fn prep_mathbox_lookup(&mut self) {
    if let Some(addr) = self.mathbox_addr {
      if self.mathbox_lookup.is_some() {
        return
      }
      let mut headers = vec![];
      for stmt in self.db.statements_range_address(addr..) {
        let StatementType::HeadingComment(HeadingLevel::Section) = stmt.statement_type() else {
          continue
        };
        let Some(hc) = stmt.as_heading_comment() else { continue };
        let buf = &**stmt.segment().segment.buffer;
        if hc.parse_mathbox_header(buf).is_some() {
          headers.push((stmt.address(), as_str(hc.header.as_ref(buf))))
        }
      }
      self.mathbox_lookup = Some(headers)
    }
  }

  pub(crate) fn build_statements(&mut self, and_headers: bool) {
    if !self.statements.is_empty() {
      return
    }
    if and_headers {
      let mut headings = [None; 4];
      let mut index = [0u16; 4];
      for stmt in self.db.statements() {
        match stmt.statement_type() {
          StatementType::HeadingComment(level) =>
            if let Some(head) = stmt.as_heading_comment() {
              let buf = &stmt.segment().segment.buffer;
              headings[level as usize - 1] = Some(Heading {
                header: as_str(head.header.as_ref(buf)).trim(),
                content: as_str(head.content.as_ref(buf)).trim(),
                stmt_num: self.statements.len(),
                level,
                index: [0; 4],
              });
            },
          StatementType::Axiom | StatementType::Provable => {
            for (i, heading) in headings.iter_mut().enumerate() {
              if let Some(heading) = heading.take() {
                index[i] += 1;
                index[i + 1..].iter_mut().for_each(|j| *j = 0);
                self.headings.push(Heading { index, ..heading })
              }
            }
            self.statements.push(stmt);
          }
          _ => {}
        }
      }
    } else {
      self.statements.extend(self.db.statements().filter(|s| s.is_assertion()))
    }
  }

  pub(crate) fn build_used_by(&mut self) {
    if self.used_by.is_some() {
      return
    }
    let mut used_by = HashMap::new();
    for &stmt in &self.statements {
      used_by.insert(stmt.label(), vec![]);
      if stmt.statement_type() == StatementType::Provable {
        let addr = stmt.address();
        for tk in UseIter::new(stmt) {
          if let Some(v) = used_by.get_mut(tk) {
            v.push(addr)
          }
        }
      }
    }
    self.used_by = Some(used_by)
  }

  pub(crate) fn build_syntax_used(&mut self) {
    if self.syntax_used.is_some() {
      return
    }
    let g = self.db.grammar_result();
    let names = self.db.name_result();
    let name_reader = &mut NameReader::new(names);
    let mut temp = BTreeSet::new();
    let iter = self.statements.iter().map(|&stmt| {
      temp.clear();
      if let Ok(fmla) = g.parse_statement(&stmt, names, name_reader) {
        temp.extend(fmla.labels_postorder_iter());
        temp.iter().copied().collect::<Box<[_]>>()
      } else {
        eprintln!("failed to parse {}", as_str(stmt.label()));
        Box::new([])
      }
    });
    self.syntax_used = Some(iter.collect())
  }

  pub(crate) fn build_recent(&mut self, num_recent: usize) {
    if self.recent.len() >= num_recent {
      return
    }
    self.recent.clear();
    let mut heap = BinaryHeap::new();
    for (s, &stmt) in self.statements.iter().enumerate() {
      let Some(comment) = stmt.associated_comment() else { continue };
      let buf = &comment.segment().segment.buffer;
      let iter = comment.parentheticals().filter_map(|(_, paren)| match paren {
        Parenthetical::ContributedBy { date, .. }
        | Parenthetical::RevisedBy { date, .. }
        | Parenthetical::ProofShortenedBy { date, .. } => Date::try_from(date.as_ref(buf)).ok(),
        _ => None,
      });
      if let Some(date) = iter.max() {
        heap.push((date, s))
      }
    }
    self.recent.extend(std::iter::from_fn(|| heap.pop()).take(num_recent))
  }

  pub(crate) fn build_recent_templates<'b>(&mut self, texts: impl Iterator<Item = &'a str>) {
    self.recent_templates.extend(texts.map(Template::parse))
  }

  fn mathbox_lookup(&self, stmt: &StatementRef<'_>) -> Option<Option<&'a str>> {
    let mbox_addr = self.mathbox_addr?;
    let addr = stmt.address();
    if self.db.cmp_address(&addr, &mbox_addr).is_lt() {
      return None
    }
    Some(match &self.mathbox_lookup {
      Some(mbs) => mbs
        .partition_point(|x| self.db.cmp_address(&x.0, &addr).is_le())
        .checked_sub(1)
        .map(|i| mbs[i].1),
      None => self.db.statements_range_address(mbox_addr..=addr).rev().find_map(|stmt| {
        let StatementType::HeadingComment(HeadingLevel::Section) = stmt.statement_type() else {
          return None
        };
        let hc = stmt.as_heading_comment()?;
        let buf = &**stmt.segment().segment.buffer;
        hc.parse_mathbox_header(buf)?;
        Some(as_str(hc.header.as_ref(buf)))
      }),
    })
  }
}

impl Renderer<'_> {
  fn pink_num(&self, space: bool, pink_num: Option<usize>) -> impl Display {
    let max = self.pink_numbers.len() as f64;
    DisplayFn(move |f| {
      if space {
        write!(f, "&nbsp;")?
      }
      if let Some(n) = pink_num {
        const PARTITIONS: usize = 28;
        const SPECTRUM: [[u8; 3]; PARTITIONS + 1] = [
          [251, 0, 0],     // 1
          [247, 12, 0],    // 10
          [238, 44, 0],    // 34
          [222, 71, 0],    // 58
          [203, 89, 0],    // 79
          [178, 108, 0],   // 109
          [154, 122, 0],   // 140
          [127, 131, 0],   // 181
          [110, 136, 0],   // 208
          [86, 141, 0],    // 242
          [60, 144, 0],    // 276
          [30, 147, 0],    // 313
          [0, 148, 22],    // 375
          [0, 145, 61],    // 422
          [0, 145, 94],    // 462
          [0, 143, 127],   // 504
          [0, 140, 164],   // 545
          [0, 133, 218],   // 587
          [3, 127, 255],   // 612
          [71, 119, 255],  // 652
          [110, 109, 255], // 698
          [137, 99, 255],  // 740
          [169, 78, 255],  // 786
          [186, 57, 255],  // 808
          [204, 33, 249],  // 834
          [213, 16, 235],  // 853
          [221, 0, 222],   // 870
          [233, 0, 172],   // 916
          [239, 0, 132],   // 948
        ];
        // [242, 0, 98],  // 973
        // [244, 0, 62],  // 1000
        let position = (n as f64 / max) * PARTITIONS as f64;
        let i = position as usize;
        assert!(i < PARTITIONS);
        let fraction = position - i as f64;
        write!(f, "<span class=r style=\"color:#")?;
        for d in 0..3 {
          write!(
            f,
            "{:02X}",
            (SPECTRUM[i][d] as f64 + fraction * (SPECTRUM[i + 1][d] as f64 - SPECTRUM[i][d] as f64))
              .round() as u8
          )?;
        }
        write!(f, "\">{n}</span>", n = n + 1)
      } else {
        write!(f, "<span class=r style=\"color:#000000\">(future)</span>")
      }
    })
  }
}

struct FrameRenderer<'a> {
  names: &'a Nameset,
  html_defs: &'a HashMap<&'a [u8], &'a str>,
  frame: &'a Frame,
}

impl<'a> Renderer<'a> {
  fn frame_renderer(&self, alt: bool, frame: &'a Frame) -> FrameRenderer<'_> {
    FrameRenderer {
      names: self.db.name_result(),
      html_defs: if alt { &self.alt_html_defs } else { &self.html_defs },
      frame,
    }
  }
}

impl<'a> FrameRenderer<'a> {
  fn verify_expr(&'a self, e: &'a VerifyExpr) -> impl Display + 'a {
    DisplayFn(|f| {
      write!(f, "<span class=math>{}", self.get_atom(e.typecode))?;
      let mut iter = TokenIter::new();
      for frag in &*e.tail {
        iter.pool = &self.frame.const_pool[frag.prefix.clone()];
        while let Some(tk) = iter.next() {
          write!(f, "{}", self.html_defs[tk])?
        }
        write!(f, "{}", self.get_atom(self.frame.var_list[frag.var]))?
      }
      iter.pool = &self.frame.const_pool[e.rump.clone()];
      while let Some(tk) = iter.next() {
        write!(f, "{}", self.html_defs[tk])?
      }
      write!(f, "</span>")
    })
  }

  fn expr(&'a self, typecode: &'a [u8], e: &'a [u8]) -> impl Display + 'a {
    DisplayFn(|f| {
      write!(f, "<span class=math>{}", self.html_defs[typecode])?;
      for tk in e.split(|&c| c == b' ').skip(1) {
        write!(f, "{}", self.html_defs[tk])?
      }
      write!(f, "</span>")
    })
  }

  fn get_atom(&self, a: Atom) -> &'a str { self.html_defs[self.names.atom_name(a)] }
}

struct TokenIter<'a> {
  pool: &'a [u8],
  buf: Vec<u8>,
}

impl<'a> TokenIter<'a> {
  fn new() -> TokenIter<'a> { TokenIter { buf: vec![], pool: &[] } }

  fn next(&mut self) -> Option<&[u8]> {
    let i = self.pool.iter().position(|&i| i & 0x80 != 0)?;
    self.buf.clear();
    self.buf.extend_from_slice(&self.pool[..=i]);
    *self.buf.last_mut().unwrap() &= 0x7f;
    self.pool = &self.pool[i + 1..];
    Some(&self.buf)
  }
}

struct Comment<'a, 'b> {
  buf: &'a str,
  r: &'b Renderer<'a>,
  html_defs: &'b HashMap<&'a [u8], &'a str>,
  html_bibliography: &'a str,
}

impl<'a> Renderer<'a> {
  fn comment(&self, buf: &'a str, alt: bool, ext: bool) -> Comment<'a, '_> {
    Comment {
      buf,
      r: self,
      html_defs: if alt { &self.alt_html_defs } else { &self.html_defs },
      html_bibliography: if ext { self.ext_html_bibliography } else { self.html_bibliography },
    }
  }
}

fn html_escape(tk: &str) -> String {
  tk.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

impl Display for Comment<'_, '_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut parser = CommentParser::new(self.buf.as_bytes(), Span::new(0, self.buf.len()));
    let mut htmls = 0;
    let mut trim_prev_ws = true;
    while let Some(item) = parser.next() {
      let mut out = vec![];
      match item {
        CommentItem::Text(sp) => {
          out.clear();
          parser.unescape_text(sp, &mut out);
          let mut s = std::str::from_utf8(&out).unwrap();
          if trim_prev_ws {
            const CLOSING_PUNCTUATION: &str = ".,;)?!:]'\"_-";
            s = s.trim_start();
            trim_prev_ws = false;
            if matches!(s.chars().next(), Some(c) if !CLOSING_PUNCTUATION.contains(c)) {
              write!(f, " ")?
            }
          }
          if htmls == 0 {
            write!(f, "{s}")?
          } else {
            write!(f, "{}", html_escape(s))?
          }
        }
        CommentItem::LineBreak(_) => {
          trim_prev_ws = true;
          write!(f, "<p>")?
        }
        CommentItem::StartMathMode(_) => write!(f, "<span {}>", self.r.html_font)?,
        CommentItem::EndMathMode(_) => {
          trim_prev_ws = true;
          write!(f, "</span>")?
        }
        CommentItem::MathToken(sp) => {
          out.clear();
          parser.unescape_math(sp, &mut out);
          write!(f, "{}", self.html_defs[&*out].trim())?
        }
        CommentItem::Label(_, sp) => {
          trim_prev_ws = true;
          out.clear();
          parser.unescape_label(sp, &mut out);
          write!(
            f,
            "<a href=\"{label}.html\">{label}</a>{pink}",
            label = as_str(&out),
            pink = self.r.pink_num(true, Some(self.r.pink_numbers[&*out])),
          )?
        }
        CommentItem::Url(_, sp) => {
          trim_prev_ws = true;
          out.clear();
          parser.unescape_label(sp, &mut out);
          write!(f, "<a href=\"{url}\">{url}</a>", url = as_str(&out))?
        }
        CommentItem::StartHtml(_) => htmls += 1,
        CommentItem::EndHtml(_) => htmls -= 1,
        CommentItem::StartSubscript(_) => write!(f, "<sub><font size=\"-1\">")?,
        CommentItem::EndSubscript(_) => write!(f, "</font></sub>")?,
        CommentItem::StartItalic(_) => write!(f, "<i>")?,
        CommentItem::EndItalic(_) => write!(f, "</i>")?,
        CommentItem::BibTag(sp) => {
          trim_prev_ws = false;
          write!(
            f,
            "[<a href=\"{file}#{tag}\">{tag}</a>]",
            file = self.html_bibliography,
            tag = as_str(sp.as_ref(self.buf.as_bytes()))
          )?
        }
      }
    }
    Ok(())
  }
}

struct VerifyExprHtml<'a> {
  fr: &'a FrameRenderer<'a>,
  e: &'a VerifyExpr,
}

impl<'a> std::ops::Deref for VerifyExprHtml<'a> {
  type Target = &'a FrameRenderer<'a>;

  fn deref(&self) -> &Self::Target { &self.fr }
}

impl Display for VerifyExprHtml<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "<span class=math>{}", self.get_atom(self.e.typecode))?;
    let mut iter = TokenIter::new();
    for frag in &*self.e.tail {
      iter.pool = &self.frame.const_pool[frag.prefix.clone()];
      while let Some(tk) = iter.next() {
        write!(f, "{}", self.html_defs[tk])?
      }
      write!(f, "{}", self.get_atom(self.frame.var_list[frag.var]))?
    }
    iter.pool = &self.frame.const_pool[self.e.rump.clone()];
    while let Some(tk) = iter.next() {
      write!(f, "{}", self.html_defs[tk])?
    }
    write!(f, "</span>")
  }
}

struct ExprHtml<'a> {
  fr: &'a FrameRenderer<'a>,
  e: &'a [u8],
}

impl Display for ExprHtml<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "<span class=math>")?;
    for tk in self.e.split(|&c| c == b' ') {
      write!(f, "{}", self.fr.html_defs[tk])?
    }
    write!(f, "</span>")
  }
}

impl<'a> Renderer<'a> {
  fn oneline_statement(&self, alt: bool, fr: &'a Frame) -> impl Display + '_ {
    let (amp, imp);
    if alt {
      amp = " &amp;";
      imp = " <span style=\"font-family: sans-serif\">&#8658;</span>";
    } else {
      amp = "<img src=\"amp.gif\" width=12 height=19 alt=\"&amp;\" align=top>";
      imp = "<img src=\"bigto.gif\" width=15 height=19 alt=\"=&gt;\" align=top>";
    }
    let frr = self.frame_renderer(alt, fr);
    DisplayFn(move |f| {
      let mut it = fr.hypotheses.iter().filter_map(|hyp| match hyp {
        Hyp::Essential(_, e) => Some(e),
        _ => None,
      });
      if let Some(mut e) = it.next() {
        loop {
          let e2 = it.next();
          write!(
            f,
            "{fmla}&nbsp;&nbsp;&nbsp;{imp}&nbsp;&nbsp;&nbsp;",
            imp = if e2.is_some() { amp } else { imp },
            fmla = frr.verify_expr(e),
          )?;
          let Some(e2) = e2 else { break };
          e = e2
        }
      }
      write!(f, "{}", frr.verify_expr(&fr.target))?;
      Ok(())
    })
  }
}

const FOOTER: &str = "\
  <table style=\"border: none; width: 100%\"><tr>\n\
    <td style=\"width: 25%\">&nbsp;</td>\n\
    <td style=\"text-align: center; vertical-align: bottom; \
      font-size: x-small; font-family: sans-serif\">\
      Copyright terms: <a href=\"../copyright.html#pd\">Public domain</a>\n\
    </td>\n\
    <td style=\"text-align: right; vertical-align: bottom; \
      width: 25%; font-size: x-small; font-family: sans-serif\">\
      <a href=\"http://validator.w3.org/check?uri=referer\">W3C validator</a>\
    </td>\n\
  </tr></table>\n";

impl<'a> Renderer<'a> {
  pub(crate) fn show_statement<W: Write>(
    &self, w: &mut W, stmt: StatementRef<'a>, alt: bool,
  ) -> io::Result<()> {
    let db = self.db;
    let ext = (self.ext_html_addr.as_ref())
      .map_or(false, |addr| db.cmp_address(addr, &stmt.address()).is_le());
    let mboxness = self.mathbox_lookup(&stmt);
    let (title_abbr, home_href, home_img) = if mboxness.is_some() {
      ("Users' Mathboxes", "mmtheorems.html#sandbox:bighdr", "_sandbox.gif")
    } else if ext {
      (&*self.ext_html_title_abbr, self.ext_html_home_href, self.ext_html_home_img)
    } else {
      (&*self.html_title_abbr, self.html_home_href, self.html_home_img)
    };
    let html_ext_url = self.html_ext_url;
    let other_dir = if alt { self.html_dir } else { self.alt_html_dir };
    let title = match mboxness {
      Some(None) => "Users' Mathboxes",
      Some(Some(header)) => header,
      None if ext => self.ext_html_title,
      None => self.html_title,
    };

    enum SubType {
      Syntax,
      Definition,
      Axiom,
      Theorem,
    }
    let is_prov = *stmt.math_at(0) == *b"|-";
    let sub_type = match stmt.statement_type() {
      StatementType::Provable => SubType::Theorem,
      StatementType::Axiom if !is_prov => SubType::Syntax,
      StatementType::Axiom if stmt.label().starts_with(b"ax-") => SubType::Axiom,
      StatementType::Axiom => SubType::Definition,
      _ => unreachable!(),
    };
    let (sub_type_upper, sub_type_lower) = match sub_type {
      SubType::Syntax => ("Syntax Definition", "syntax"),
      SubType::Definition => ("Definition", "definition"),
      SubType::Axiom => ("Axiom", "axiom"),
      SubType::Theorem => ("Theorem", "theorem"),
    };
    let label = stmt.label();
    let s_label = as_str(label);
    let seg = stmt.segment().segment;
    let comment = stmt.associated_comment().unwrap().comment_contents().as_ref(&seg.buffer);
    let comment = self.comment(as_str(comment).trim(), alt, ext && mboxness.is_none());

    let cur = stmt.address();
    let (prev, wrap_prev) = match db.statements_range_address(..cur).rfind(|s| s.is_assertion()) {
      Some(prev) => (prev, false),
      None => (db.statements().rfind(|s| s.is_assertion()).unwrap(), true),
    };
    let (next, wrap_next) = match db
      .statements_range_address((Bound::Excluded(cur), Bound::Unbounded))
      .find(|s| s.is_assertion())
    {
      Some(next) => (next, false),
      None => (db.statements().find(|s| s.is_assertion()).unwrap(), true),
    };

    writeln!(
      w,
      "<!DOCTYPE html>\n\
      <html lang=\"en-us\"><head>\n\
        <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">\n\
        <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n\
        <style>\n\
        img {{ border: 0; margin-bottom: -4px; }}\n\
        .steps {{ \
          text-align: center; border-spacing: 0; background-color: {bgcolor}; \
          margin: auto; \
          border: outset 1px {border_color}; \
        }}\n\
        .steps td, .steps th {{ border: inset 1px {border_color}; }}\n\
        .steps th {{ text-align: center; }}\n\
        .steps td {{ text-align: left; }}\n\
        .title {{ font-weight: bold; color: {title_color}; }}\n\
        .bottom-table {{ \
          text-align: center; border-spacing: 5px; \
          margin: auto; \
        }}\n\
        .bottom-table td {{ text-align: left; font-size: small; }}\n\
        hr {{ border-style: solid; border-top: 1px; }}\n\
        .r {{ font-family: \"Arial Narrow\"; font-size: x-small; }}\n\
        .i {{ font-family: \"Arial Narrow\"; font-size: x-small; color: gray; }}\n\
        .comment p {{ margin-bottom: 0 }}\n\
        </style>\n\
        {css}\n\
        <title>{label} - {title}</title>\n\
        <link rel=\"shortcut icon\" href=\"favicon.ico\" type=\"image/x-icon\">\n\
      </head><body style=\"background-color: #FFFFFF\">\n\
        <table style=\"border-spacing: 0; width: 100%\">\n\
          <tr>\n\
            <td style=\"padding: 0; text-align: left; vertical-align: top; width: 25%\">\n\
              <a href=\"{home_href}\">\n\
                <img src=\"{home_img}\" alt=\"{title_abbr}\" title=\"{title_abbr}\" \
                  height=32 width=32 style=\"vertical-align: top; margin-bottom: 0px\">\n\
              </a>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: center; vertical-align: top\" colspan=2>\n\
              <span style=\"font-size: xx-large\">{title}</span>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: right; vertical-align: top; width: 25%; \
                font-size: x-small; font-family: sans-serif\">\n\
              <span style=\"font-size: small\">\n\
                <a href=\"{prev}.html\">&lt; {prev_text}</a>&nbsp;&nbsp;\n\
                <a href=\"{next}.html\">{next_text} &gt;</a>\n\
              </span><br>\
              <a href=\"mmtheorems{page}.html#{label}\">Nearby theorems</a>\n\
            </td>\n\
          </tr><tr style=\"font-size: x-small; font-family: sans-serif; vertical-align: top\">\n\
            <td style=\"padding: 0; text-align: left\" colspan=2>\
              <a href=\"../mm.html\">Mirrors</a>&nbsp; &gt; &nbsp;\
              <a href=\"../index.html\">Home</a>&nbsp; &gt; &nbsp;\
              <a href=\"{home_href}\">{title_abbr}</a>&nbsp; &gt; &nbsp;\
              <a href=\"mmtheorems.html\">Th. List</a>&nbsp; &gt; &nbsp;\
              {mbox}{label}\
            </td>\n\
            <td style=\"padding: 0; text-align: right\" colspan=2>\
              {html_ext_url}\
              <a href=\"{other_dir}{label}.html\">{other_name} version</a>\
            </td>\n\
          </tr>\n\
        </table>\n\
        <hr>\n\
        <div style=\"text-align: center\">\n\
          <b style=\"font-size: large\">\
            {sub_type} <span class=title>{label}</span>\
          </b>{pink_html}\
        </div>\n\
        <div style=\"text-align: center; padding: 3px\">\n\
          <div class=comment style=\"text-align: left; display: inline-block\">\
            <b>Description: </b>{comment}\
          </div>\n\
        </div>",
      border_color = GRAY_BORDER_COLOR,
      bgcolor = MINT_BACKGROUND_COLOR,
      css = &*self.html_css,
      label = s_label,
      title_color = GREEN_TITLE_COLOR,
      prev = as_str(prev.label()),
      prev_text = if wrap_prev { "Wrap" } else { "Previous" },
      next = as_str(next.label()),
      next_text = if wrap_next { "Wrap" } else { "Next" },
      page = self.pink_numbers[stmt.label()] / THMS_PER_PAGE + 1,
      mbox = if mboxness.is_some() {
        "<a href=\"mmtheorems.html#sandbox:bighdr\">Mathboxes</a>&nbsp; &gt; &nbsp;"
      } else {
        ""
      },
      html_ext_url = html_ext_url.replace('*', s_label),
      other_name = if alt { "GIF" } else { "Unicode" },
      sub_type = sub_type_upper,
      pink_html = self.pink_num(true, Some(self.pink_numbers[stmt.label()])),
    )?;

    let scope = db.scope_result();
    let fr = scope.get(stmt.label()).unwrap();
    let frr = self.frame_renderer(alt, fr);
    let num_hyps = match sub_type {
      SubType::Syntax => fr.hypotheses.len(),
      _ => fr.hypotheses.iter().filter(|h| matches!(h, Hyp::Essential(..))).count(),
    };
    if num_hyps != 0 {
      writeln!(
        w,
        "<table class=steps>\n\
          <caption><b>Hypothes{es}</b></caption>\n\
          <tr><th>Ref</th><th>Expression</th></tr>",
        es = if num_hyps == 1 { "is" } else { "es" },
      )?;
      for hyp in &*fr.hypotheses {
        match (&sub_type, hyp) {
          (_, &Hyp::Essential(s, ref e)) => {
            let s = db.statement_by_address(s);
            writeln!(
              w,
              "<tr><td>{label}</td><td class=math>{fmla}</td></tr>",
              label = as_str(s.label()),
              fmla = frr.verify_expr(e),
            )?
          }
          (SubType::Syntax, &Hyp::Floating(s, ..)) => {
            let s = db.statement_by_address(s);
            writeln!(
              w,
              "<tr><td>{label}</td><td class=math><span class=math>{tc}{var}</span></td></tr>",
              label = as_str(s.label()),
              tc = frr.html_defs[&*s.math_at(0)],
              var = frr.html_defs[&*s.math_at(1)],
            )?
          }
          _ => {}
        }
      }
      writeln!(w, "</table>")?;
    }
    writeln!(
      w,
      "<table class=steps>\n\
        <caption><b>Assertion</b></caption>\n\
        <tr><th>Ref</th><th>Expression</th></tr>\n\
        <tr>\n\
          <td class=title>{label}</td>\n\
          <td class=math>{expr}</td>\n\
        </tr>
      </table>",
      label = s_label,
      expr = frr.verify_expr(&fr.target)
    )?;

    let names =
      fr.var_list.iter().map(|&v| as_str(db.name_result().atom_name(v))).collect::<Box<[_]>>();
    if !fr.mandatory_dv.is_empty() {
      let mut dvs = approximate_clique_cover(fr.mandatory_count, &fr.mandatory_dv);
      dvs.retain(|cl| cl.len() > 1);
      dvs.iter_mut().for_each(|cl| cl.sort_unstable_by_key(|&i| names[i]));
      dvs.sort_by_cached_key(|cl| cl.iter().map(|&i| names[i]).collect::<Box<[_]>>());
      write!(
        w,
        "<div style=\"text-align: center\">\
          <a href=\"/mpeuni/mmset.html#distinct\">Distinct variable</a> group{s}: ",
        s = if dvs.len() == 1 { "" } else { "s" },
      )?;
      write!(w, "<span class=math>")?;
      for cl in dvs {
        write!(w, " &nbsp; {}", cl.iter().map(|&v| frr.html_defs[names[v].as_bytes()]).format(","))?
      }
      write!(w, "</span></div>")?;

      // allowed substitution hints (set.mm specific)
      if !matches!(sub_type, SubType::Syntax) {
        let mut fovars = vec![];
        let mut sovars = vec![];
        for hyp in &*fr.hypotheses {
          if let Hyp::Floating(_, i, atom) = *hyp {
            if self.first_order_tc.contains(&atom) {
              fovars.push((i, true))
            }
            if self.second_order_tc.contains(&atom) {
              sovars.push(i)
            }
          }
        }
        fovars.sort_unstable_by_key(|&(i, _)| names[i]);
        sovars.sort_unstable_by_key(|&i| names[i]);
        let mut count = 0;
        let mut output = String::new();
        for v in sovars {
          fovars.iter_mut().for_each(|p| p.1 = true);
          for &(a, b) in &*fr.mandatory_dv {
            let u = if a == v {
              b
            } else if b == v {
              a
            } else {
              continue
            };
            if let Some(p) = fovars.iter_mut().find(|p| p.0 == u) {
              p.1 = false
            }
          }
          if fovars.iter().any(|p| p.1) {
            use std::fmt::Write;
            count += 1;
            write!(
              &mut output,
              " &nbsp; {}({})",
              frr.html_defs[names[v].as_bytes()],
              fovars
                .iter()
                .filter(|p| p.1)
                .map(|&x| frr.html_defs[names[x.0].as_bytes()])
                .format(",")
            )
            .unwrap()
          }
        }
        if !output.is_empty() {
          write!(
            w,
            "<div style=\"text-align: center\">\
              <a href=\"/mpeuni/mmset.html#allowedsubst\">Allowed substitution</a> hint{s}: \
              <span class=math>{output}</span>\
            </div>",
            s = if count == 1 { "" } else { "s" },
          )?;
        }
      }
    }
    writeln!(w, "<hr>")?;

    let mut syntax = vec![];
    let write_colors = |w: &mut W| {
      writeln!(
        w,
        "<table class=bottom-table>\n\
          <tr><td><b>Colors of variables:</b> {var_color}</td></tr>",
        var_color = self.html_var_color,
      )
    };
    let is_thm = matches!(sub_type, SubType::Theorem);
    if matches!(sub_type, SubType::Syntax) {
      if let Some(s) =
        db.statements_range_address((Bound::Excluded(cur), Bound::Unbounded)).find(|s| {
          s.statement_type() == StatementType::Axiom && *s.math_at(0) == *b"|-" && {
            let fr2 = scope.get(stmt.label()).unwrap();
            fr.target.const_ranges().all(|sp| {
              sp.is_empty() || {
                let sp = &fr.const_pool[sp];
                (fr2.target.const_ranges())
                  .any(|sp2| fr2.const_pool[sp2].windows(sp.len()).contains(&sp))
              }
            })
          }
        })
      {
        let name = as_str(s.label());
        let (pre, post) = if name.starts_with("ax-") {
          ("This syntax is primitive.  The first axiom using it is ", "")
        } else {
          ("See definition ", " for more information")
        };
        writeln!(
          w,
          "<div style=\"text-align: center\">\
            {pre}<a href=\"{name}.html\">{name}</a>{post}</div>\n\
          <hr>"
        )?;
      }
    } else {
      let mut proof = ProofTreeArray::default();
      let proof_ok = if is_thm {
        let thm_header = format!("<b>Proof of Theorem <span class=title>{s_label}</span></b>");
        let mut dummies =
          if (fr.mandatory_count..fr.optional_dv.len()).all(|i| fr.optional_dv[i].is_empty()) {
            vec![]
          } else {
            let vars = UseIter::new(stmt)
              .filter_map(|s| scope.get(s))
              .filter(|fr| fr.stype == StatementType::Floating)
              .map(|fr| fr.var_list[0])
              .collect::<HashSet<_>>();
            (fr.mandatory_count..fr.optional_dv.len())
              .filter(|&i| !fr.optional_dv[i].is_empty() && vars.contains(&fr.var_list[i]))
              .collect::<Vec<_>>()
          };
        if !dummies.is_empty() {
          dummies.sort_by_key(|&i| names[i]);
          writeln!(w, "<div style=\"text-align: center\">{thm_header}</div>\n")?;
          writeln!(
            w,
            "<div style=\"text-align: center\">\
              <a href=\"/mpeuni/mmset.html#dvnote1\">Dummy variable{s}</a> \
              <span class=math>{dummies}</span> {is} distinct from all other variables.</div>",
            s = if dummies.len() == 1 { "" } else { "s" },
            dummies = dummies.iter().map(|&v| frr.html_defs[names[v].as_bytes()]).format(" "),
            is = if dummies.len() == 1 { "is" } else { "are mutually distinct and" },
          )?;
          writeln!(w, "<table class=steps>")?
        } else {
          writeln!(w, "<table class=steps>\n<caption>{thm_header}</caption>")?;
        }
        if let Ok(qed) = db.verify_one(&mut proof, stmt) {
          proof.qed = qed;
          true
        } else {
          false
        }
      } else {
        writeln!(
          w,
          "<table class=steps>\n\
            <caption><b>Detailed syntax breakdown of {sub_type_upper} \
              <span class=title>{s_label}</span></b></caption>"
        )?;
        let g = db.grammar_result();
        let mut typecode = frr.names.get_atom(stmt.math_at(0).slice);
        let provable = typecode == g.provable_typecode();
        if provable {
          typecode = g.logic_typecode()
        }
        let names = &mut NameReader::new(frr.names);
        match g.parse_formula(&mut stmt.token_iter(names), &[typecode], provable, frr.names) {
          Ok(fmla) => {
            proof.qed = fmla.as_ref(db).build_syntax_proof(&mut vec![], &mut proof);
            true
          }
          Err(_) => {
            eprintln!("failed to parse {s_label}");
            false
          }
        }
      };

      writeln!(w, "<tr><th>Step</th><th>Hyp</th><th>Ref</th><th>Expression</th></tr>")?;

      if proof_ok {
        let mut order = CalcOrder::new(db, &proof, is_thm && is_prov);
        order.step(proof.qed, 0);
        for (step, &(i, indent)) in order.order.iter().enumerate() {
          let tree = &proof.trees[i];
          let expr = &proof.exprs().unwrap()[i];
          let ref_stmt = db.statement_by_address(tree.address);
          let hyp = DisplayFn(|f| {
            let mut iter = tree
              .children
              .iter()
              .map(|&i| order.reverse[i])
              .filter(|&i| i != SKIPPED_STEP)
              .peekable();
            if iter.peek().is_some() {
              let iter = iter.map(|i| DisplayFn(move |f| write!(f, "<a href=\"#{i}\">{i}</A>")));
              write!(f, "{}", iter.format(", "))
            } else {
              write!(f, "&nbsp;")
            }
          });

          writeln!(w, "<tr><td>{step}</td>\n<td>{hyp}</td>", step = step + 1)?;
          if ref_stmt.is_assertion() {
            writeln!(
              w,
              "<td><a href=\"{ref_label}.html\" title=\"{descr}\">{ref_label}</a>{pink}</td>",
              ref_label = as_str(ref_stmt.label()),
              descr = as_str(&abbrev_desc(ref_stmt, 87, false)).replace('\"', "'"),
              pink = self.pink_num(true, Some(self.pink_numbers[ref_stmt.label()])),
            )?;
          } else {
            writeln!(w, "<td>{}</td>", as_str(ref_stmt.label()))?;
          }
          write!(w, "<td class=math><span class=i>")?;
          (0..indent).try_for_each(|_| write!(w, ". "))?;
          writeln!(
            w,
            "{indent}</span>\n{fmla}</td></tr>",
            indent = indent + 1,
            fmla = frr.expr(&ref_stmt.math_at(0), expr)
          )?
        }

        if is_thm {
          let mut addrs = proof.trees.iter().map(|tree| tree.address).collect::<HashSet<_>>();
          let mut atoms = HashSet::new();
          let names = &mut NameReader::new(frr.names);
          let g = db.grammar_result();
          for &addr in &addrs {
            let stmt = db.statement_by_address(addr);
            if let Some(syntax_used) = &self
              .syntax_used
              .as_ref()
              .and_then(|syntax_used| Some(&syntax_used[*self.pink_numbers.get(stmt.label())?]))
            {
              atoms.extend(syntax_used.iter().copied())
            } else {
              match g.parse_statement(&stmt, frr.names, names) {
                Ok(fmla) => atoms.extend(fmla.labels_postorder_iter()),
                Err(_) => eprintln!("failed to parse {}", as_str(stmt.label())),
              }
            }
          }
          for atom in atoms {
            let token = frr.names.atom_name(atom);
            addrs.insert(frr.names.lookup_label(token).unwrap().address);
          }
          syntax = addrs
            .into_iter()
            .map(|addr| db.statement_by_address(addr))
            .filter_map(|stmt| self.syntax_hint.get(stmt.label()).map(|c| (stmt.label(), c)))
            .collect_vec()
        }
      } else {
        writeln!(
          w,
          "<tr><td colspan=4 style=\"color: red\"><b>\
            WARNING: Proof has a severe error.\
          </b></td></tr>"
        )?
      }
      writeln!(w, "</table>")?;
    }

    write_colors(w)?;

    if !syntax.is_empty() {
      syntax.sort_by_key(|(stmt, _)| self.pink_numbers[stmt]);
      write!(w, "<tr><td><b>Syntax hints:</b> ")?;
      for (label, c) in syntax {
        write!(
          w,
          " &nbsp;<span class=math>{tk}</span><A HREF=\"{label}.html\">{label}</A>{pink}",
          tk = frr.html_defs[&**c],
          pink = self.pink_num(true, Some(self.pink_numbers[label])),
          label = as_str(label)
        )?;
      }
      writeln!(w, "</td></tr>")?;
    }

    if is_thm {
      let mut usage = self
        .trace_usage
        .lock()
        .unwrap()
        .get(db, label)
        .iter()
        .filter_map(|&ax| db.statement(ax))
        .sorted_by_key(|stmt| self.pink_numbers[stmt.label()])
        .collect_vec();

      let mut axioms = vec![];
      let mut defs = vec![];
      usage.retain(|stmt| {
        stmt.statement_type() != StatementType::Axiom || {
          let name = as_str(stmt.label());
          if name.starts_with("ax-") {
            axioms.push(name);
            false
          } else if name.starts_with("df-") {
            defs.push(name);
            false
          } else {
            *stmt.math_at(0) == *b"|-"
          }
        }
      });

      let mut write_list = |header: &str, labels: Vec<&str>| -> io::Result<_> {
        if !labels.is_empty() {
          writeln!(w, "<tr><td><b>{header}:</b>")?;
          for label in labels {
            writeln!(
              w,
              "&nbsp;<A HREF=\"{label}.html\">{label}</A>{pink}",
              label = label,
              pink = self.pink_num(true, Some(self.pink_numbers[label.as_bytes()])),
            )?
          }
          writeln!(w, "</td></tr>")?;
        }
        Ok(())
      };
      write_list("This theorem was proved from axioms", axioms)?;
      write_list("This theorem depends on definitions", defs)?;

      if !usage.is_empty() {
        if matches!(*usage, [stmt] if stmt.label() == label) {
          writeln!(
            w,
            "<tr><td style=\"font-size: normal; color: #FF6600\">&nbsp;<b>\
              WARNING: This theorem has an incomplete proof.</b><br></td></tr>"
          )?
        } else {
          writeln!(
            w,
            "<tr><td style=\"font-size: normal; color: #FF6600\">&nbsp;<b>\
              WARNING: This proof depends on the following unproved theorem(s): "
          )?;
          for stmt in usage {
            writeln!(w, " <a href=\"{label}.html\">{label}</a>", label = as_str(stmt.label()))?
          }
          writeln!(w, "</b></td></tr>")?;
        }
      }
    }

    if !matches!(sub_type, SubType::Syntax) {
      writeln!(w, "<tr><td><b>This {sub_type_lower} is referenced by:</b>")?;
      let mut empty = true;
      let mut write_one = |label| {
        empty = false;
        writeln!(
          w,
          "&nbsp;<a href=\"{label}.html\">{label}</a>{pink}",
          label = as_str(label),
          pink = self.pink_num(true, Some(self.pink_numbers[label])),
        )
      };
      if let Some(used_by) = &self.used_by {
        for &addr in &used_by[stmt.label()] {
          write_one(db.statement_by_address(addr).label())?
        }
      } else {
        for s in db.statements_range_address((Bound::Excluded(stmt.address()), Bound::Unbounded)) {
          if is_direct_use(&s, label) {
            write_one(s.label())?
          }
        }
      }
      if empty {
        writeln!(w, " (None)")?
      }
      writeln!(w, "</td></tr>")?;
    }
    writeln!(w, "</table>")?;

    writeln!(w, "{FOOTER}</body></html>")
  }

  pub(crate) fn show_theorems<W: Write>(
    &self, w: &mut W, page: Option<usize>, num_pages: usize, alt: bool,
  ) -> io::Result<()> {
    let db = self.db;
    let has_mmrecent = self.mathbox_addr.is_some();
    let mmtheorem = |page| {
      DisplayFn(move |f| match page {
        Some(page) => write!(f, "mmtheorems{}", page + 1),
        None => write!(f, "mmtheorems"),
      })
    };
    let prev = match page {
      Some(0) => None,
      Some(page) => Some(page - 1),
      None => num_pages.checked_sub(1),
    };
    let next = match page.map_or(0, |page| page + 1) {
      page if page + 1 == num_pages => None,
      page => Some(page),
    };
    let prev_next = format!(
      "<a href=\"{prev}.html\">&lt; {prev_text}</a>&nbsp;&nbsp;\
      <a href=\"{next}.html\">{next_text} &gt;</a>\n",
      prev = mmtheorem(prev),
      prev_text = if page.is_none() { "Wrap" } else { "Previous" },
      next = mmtheorem(next),
      next_text = if next.is_none() { "Wrap" } else { "Next" },
    );
    writeln!(
      w,
      "<!DOCTYPE html>\n\
      <html lang=\"en-us\"><head>\n\
        <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">\n\
        <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n\
        <style>\n\
        img {{ border: 0; margin-bottom: -4px; }}\n\
        .r {{ font-family: \"Arial Narrow\"; font-size: x-small; }}\n\
        .top td {{ padding: 1px; }}\n\
        .color-key td {{ padding: 5px; }}\n\
        .thlist {{ \
          border-spacing: 0; margin: auto; background-color: {bgcolor}; \
          border: outset 1px {border_color}; \
        }}\n\
        .title {{ font-weight: bold; color: {title_color}; }}\n\
        hr {{ border: 1px solid gray; border-bottom: 0; }}\n\
        .thlist td, .thlist th {{ padding: 3px; border: inset 1px {border_color}; }}\n\
        .sp {{ background-color: white; }}\n\
        .sp td {{ font-size: x-small; }}\n\
        .th {{ white-space: nowrap; }}\n\
        .stx {{ white-space: nowrap; font-weight: bold; color: #00CC00; }}\n\
        .ax {{ white-space: nowrap; font-weight: bold; color: red; }}\n\
        .df {{ white-space: nowrap; font-weight: bold; color: blue; }}\n\
        .comment p {{ margin-bottom: 0; }}\n\
        .heading {{ background-color: #FFFFF2; }}\n\
        .heading h1, .heading h2 {{ font-size: large; text-align: center; margin: 0; }}\n\
        .heading h3, .heading h4 {{ font-size: medium; text-align: center; margin: 0; }}\n\
        .ext {{ background-color: {PURPLISH_BIBLIO_COLOR}; }}\n\
        .sbox {{ background-color: {SANDBOX_COLOR}; }}\n\
        </style>\n\
        {css}\n\
        <title>P. {page} of Theorem List - {title}</title>\n\
        <link rel=\"shortcut icon\" href=\"favicon.ico\" type=\"image/x-icon\">\n\
      </head><body style=\"background-color: #FFFFFF\">\n\
        <table class=top style=\"width: 100%\">\n\
          <tr>\n\
            <td style=\"text-align: left; vertical-align: top; width: 25%; \
                font-size: x-small; font-family: sans-serif\" rowspan=2>\
              {html_home}\
            </td>\n\
            <td class=title style=\"text-align: center; white-space: nowrap\" rowspan=2>\n\
              <span style=\"font-size: xx-large\">{title}</span><br>\n\
              <span style=\"font-size: x-large\">Theorem List ({subtitle})</span>\n\
            </td>\n\
            <td style=\"text-align: right; vertical-align: top; white-space: nowrap; \
                width: 25%; font-size: small; font-family: sans-serif\">\n\
              {prev_next}\
            </td>\n\
          </tr><tr>\n\
            <td style=\"text-align: right; font-size: x-small; font-family: sans-serif\">\
              {other_flavor} Try the<br>\n\
              <a href=\"{other_dir}{page_name}\">{other_name} version</a>.\
            </td>\n\
          </tr><tr style=\"font-size: x-small; font-family: sans-serif; vertical-align: top\">\n\
            <td style=\"text-align: left\" colspan=3>\n\
              <br>\n\
              <a href=\"../mm.html\">Mirrors</a>&nbsp; &gt; &nbsp;\
              <a href=\"../index.html\">Metamath Home Page</a>&nbsp; &gt; &nbsp;\
              <a href=\"{bib_href}\">{title_abbr} Page</a>&nbsp; &gt; &nbsp;\
              {top_thm_link}{mmrecent} &nbsp; &nbsp; &nbsp;\n\
              <span class=title> This page:</span>\n\
              {dtoc_link}\
              <a href=\"#mmpglst\">Page List</a>\n\
            </td>\n\
          </tr>\n\
        </table>\n\
        <hr>",
      bgcolor = MINT_BACKGROUND_COLOR,
      border_color = GRAY_BORDER_COLOR,
      css = &*self.html_css,
      page = DisplayFn(|f| match page {
        Some(page) => write!(f, "{}", page + 1),
        None => write!(f, "TOC"),
      }),
      title = self.html_title,
      html_home = self.html_home,
      title_color = GREEN_TITLE_COLOR,
      subtitle = DisplayFn(|f| match page {
        Some(page) => write!(f, "p. {} of {num_pages}", page + 1),
        None => write!(f, "Table of Contents"),
      }),
      other_flavor = if alt { "Bad symbols?" } else { "Browser slow?" },
      other_name = if alt { "GIF" } else { "Unicode" },
      other_dir = if alt { self.html_dir } else { self.alt_html_dir },
      page_name = mmtheorem(page),
      bib_href = self.html_bibliography,
      title_abbr = self.html_title_abbr,
      top_thm_link = match page {
        Some(_) => "<a href=\"mmtheorems.html\">Theorem List Contents</a>",
        None => "Theorem List Contents",
      },
      mmrecent = match has_mmrecent {
        true => "&nbsp; &gt; &nbsp;\n<a href=\"mmrecent.html\">Recent Proofs</a>",
        false => "",
      },
      dtoc_link = match page {
        Some(_) => "",
        None => "<a href=\"#mmdtoc\">Detailed Table of Contents</a>&nbsp;\n",
      },
    )?;

    let end = self.statements.len();
    if let Some(page) = page {
      writeln!(w, "<span id=\"mmstmtlst\"></span>")?;
      let get_pink = |addr| Some(*self.pink_numbers.get(db.statement_by_address(addr).label())?);
      let mathbox_num = self.mathbox_addr.and_then(get_pink).unwrap_or(end);
      let ext_html_num =
        self.ext_html_addr.and_then(get_pink).unwrap_or(mathbox_num).min(mathbox_num);

      if self.ext_html_addr.is_some() || self.mathbox_addr.is_some() {
        writeln!(
          w,
          "<p>\n\
          <table class=color-key style=\"border-spacing: 0; margin: auto\"><tr>\n\
            <td style=\"padding: 5px\">Color key:&nbsp;&nbsp;&nbsp;</td>"
        )?;
        let mut write_td = |(from, to), bgcolor, (title, href, img)| {
          writeln!(
            w,
            "<td style=\"background-color: {bgcolor}; white-space: nowrap\">\
              <a href=\"{href}\">\
                <img src=\"{img}\" style=\"vertical-align: middle\" \
                    alt=\"{title}\" height=32 width=32> \
                &nbsp;{title}\
              </a><br>\n\
              ({from}-{to})\
            </td>\n\
            <td style=\"width: 10px\">&nbsp;</td>",
            from = self.pink_num(false, Some(from)),
            to = self.pink_num(false, Some(to)),
          )
        };
        if 0 < ext_html_num {
          write_td(
            (0, ext_html_num - 1),
            MINT_BACKGROUND_COLOR,
            (self.html_title, self.html_home_href, self.html_home_img),
          )?
        }
        if ext_html_num < mathbox_num {
          write_td(
            (ext_html_num, mathbox_num - 1),
            PURPLISH_BIBLIO_COLOR,
            (self.ext_html_title, self.ext_html_home_href, self.ext_html_home_img),
          )?
        }
        if mathbox_num < end {
          write_td(
            (mathbox_num, end - 1),
            SANDBOX_COLOR,
            ("Users' Mathboxes", "mathbox.html", "_sandbox.gif"),
          )?
        }
        writeln!(w, "</tr></table>")?;
      }

      let from = page * THMS_PER_PAGE;
      let to = ((page + 1) * THMS_PER_PAGE).min(self.statements.len());
      writeln!(
        w,
        "<p>\n\
        <table class=thlist>\n\
          <caption>\
            <b>Theorem List for {title} - </b>{from}<b>-</b>{to} &nbsp; \
            *Has distinct variable group(s)\
          </caption>\n\
          <tr><th>Type</th><th>Label</th><th>Description</th></tr>\n\
          <tr><th colspan=3>Statement</th></tr>\n\
          <tr class=sp><td colspan=3>&nbsp;</td></tr>",
        title = self.html_title,
        from = self.pink_num(false, Some(from)),
        to = self.pink_num(false, to.checked_sub(1)),
      )?;

      let mut h_idx = self.headings.partition_point(|h| h.stmt_num < from);
      let scope = db.scope_result();
      for s in from..to {
        let stmt = self.statements[s];
        let buf = &stmt.segment().segment.buffer;
        let desc = stmt.associated_comment().unwrap().comment_contents();
        let ext = ext_html_num <= s;
        let mboxness = self.mathbox_lookup(&stmt);
        let fr = scope.get(stmt.label()).unwrap();
        writeln!(w)?;
        while let Some(h) = self.headings.get(h_idx).filter(|h| h.stmt_num == s) {
          let (tag, kind) = match h.level {
            HeadingLevel::MajorPart => ("h1", "h"),
            HeadingLevel::Section => ("h2", "b"),
            HeadingLevel::SubSection => ("h3", "s"),
            HeadingLevel::SubSubSection => ("h4", "t"),
            HeadingLevel::Database | HeadingLevel::Statement => unreachable!(),
          };
          writeln!(
            w,
            "<tr class=heading><td colspan=3>\
              <{tag} id=\"mm{stmt_num}{kind}\">{hdr}</{tag}>",
            stmt_num = s + 1,
            hdr = h.header()
          )?;
          if !h.content.is_empty() {
            writeln!(
              w,
              "<div class=comment><p>{comment}</div>",
              comment = self.comment(h.content, alt, ext && mboxness.is_none(),)
            )?;
          }
          writeln!(w, "</td></tr>")?;
          writeln!(w, "<tr class=sp><td colspan=3>&nbsp;</td></tr>")?;
          h_idx += 1;
        }
        let bgclass = DisplayFn(|f| {
          if ext {
            write!(f, " class={}", if s < mathbox_num { "ext" } else { "sbox" })?
          }
          Ok(())
        });
        let (kind_class, kind) = if stmt.statement_type() == StatementType::Provable {
          ("th", "Theorem")
        } else if stmt.label().starts_with(b"ax-") {
          ("ax", "Axiom")
        } else if stmt.label().starts_with(b"df-") {
          ("df", "Definition")
        } else {
          ("stx", "Syntax")
        };
        writeln!(
          w,
          "<tr id=\"{label}\"{bgclass}>\
            <td class={kind_class}>{kind}</td>\
            <td style=\"text-align: center\"><a href=\"{label}.html\">{label}</a>{pink}{dv}</td>\
            <td class=comment style=\"text-align: left\">{comment}</td>\
          </tr>\
          <tr{bgclass}><td colspan=3 style=\"text-align: center\" class=math>{frame}</td></tr>",
          label = as_str(stmt.label()),
          pink = self.pink_num(true, Some(s)),
          dv = if fr.mandatory_dv.is_empty() { "" } else { "*" },
          comment = self.comment(as_str(desc.as_ref(buf)).trim(), alt, ext && mboxness.is_none()),
          frame = self.oneline_statement(alt, fr),
        )?;
        if s + 1 < to {
          writeln!(w, "<tr class=sp><td colspan=3>&nbsp;</td></tr>")?;
        }
      }
      writeln!(w, "</table>")?;
    } else {
      let mut toc_buf = vec![];
      let mut dtoc_buf = vec![];
      let mut comment_anchor = {
        let mut last = usize::MAX;
        move |b, s| {
          let b = b && last != s;
          if b {
            last = s
          }
          let stmts = &self.statements;
          DisplayFn(move |f| {
            if b {
              write!(f, "<a id=\"{}\"></a>", as_str(stmts[s].label()))
            } else {
              Ok(())
            }
          })
        }
      };
      let mut mbox_anchor = {
        let mut done = self.mathbox_addr;
        let stmts = &self.statements;
        move |s: usize| match done {
          Some(a) if stmts[s].address() == a => {
            done = None;
            format_args!("<a id=\"sandbox:bighdr\"></a>")
          }
          _ => format_args!(""),
        }
      };
      for h in &self.headings {
        let Heading { header, content, level, stmt_num, .. } = *h;
        let idx = h.idx();
        let i = level as usize - 1;
        let url = DisplayFn(|f| {
          write!(
            f,
            "mmtheorems{page}.html#mm{num}",
            page = stmt_num / THMS_PER_PAGE + 1,
            num = stmt_num + 1
          )
        });
        let (part, kind) = match level {
          HeadingLevel::MajorPart => ("PART ", "h"),
          HeadingLevel::Section => ("", "b"),
          HeadingLevel::SubSection => ("", "s"),
          HeadingLevel::SubSubSection => ("", "t"),
          HeadingLevel::Database | HeadingLevel::Statement => unreachable!(),
        };
        let indent = DisplayFn(|f| (0..i).try_for_each(|_| write!(f, "&nbsp; &nbsp; &nbsp; ")));
        match level {
          HeadingLevel::MajorPart | HeadingLevel::Section => {
            let hdr = DisplayFn(|f| write!(f, "{part}{idx}&nbsp;&nbsp;{header}"));
            writeln!(
              toc_buf,
              "{indent}{mbox}\
              <a href=\"#dtl:{idx}\"><b>{hdr}</b></a><br>",
              mbox = mbox_anchor(stmt_num),
            )?;
            writeln!(
              dtoc_buf,
              "{indent}\
              {comment}<a id=\"dtl:{idx}\" href=\"{url}{kind}\"><b>{mark}{hdr}</b></a><br>",
              comment = comment_anchor(!content.is_empty(), stmt_num),
              mark = if content.is_empty() { "" } else { "*" },
            )?;
          }
          HeadingLevel::SubSection | HeadingLevel::SubSubSection => {
            let hdr = DisplayFn(|f| write!(f, "{idx}&nbsp;&nbsp;{header}"));
            writeln!(
              dtoc_buf,
              "{indent}{comment}\
              <a href=\"{url}{kind}\">{mark}{hdr}</a> &nbsp; \
              <a href=\"{label}.html\">{label}</a>{pink}<br>",
              comment = comment_anchor(!content.is_empty(), stmt_num),
              mark = if content.is_empty() { "" } else { "*" },
              label = as_str(self.statements[stmt_num].label()),
              pink = self.pink_num(true, Some(stmt_num)),
            )?;
          }
          HeadingLevel::Database | HeadingLevel::Statement => unreachable!(),
        }
      }
      writeln!(
        w,
        "<p><div style=\"font-weight: bold; text-align: center\">Table of Contents Summary</div>"
      )?;
      w.write_all(&toc_buf)?;
      writeln!(w, "<hr>")?;
      writeln!(
        w,
        "<p><div id=\"mmdtoc\" style=\"font-weight: bold; text-align: center\">\n\
          Detailed Table of Contents<br>\n\
          (* means the section header has a description)\n\
        </div>"
      )?;
      w.write_all(&dtoc_buf)?;
      writeln!(w, "<hr>")?;
    }
    writeln!(
      w,
      "<div style=\"text-align: right; font-size: small; font-family: sans-serif; padding: 3px\">\
        {prev_next}\
      </div>\n\
      <hr>\n\
      <div id=\"mmpglst\" style=\"font-weight: bold; text-align: center\">Page List</div>\n\
      Jump to page: "
    )?;
    if page.is_none() {
      writeln!(w, "Contents&nbsp;")
    } else {
      writeln!(w, "<a href=\"mmtheorems.html\">Contents</a>&nbsp;")
    }?;
    for p in 0..num_pages {
      let n = p + 1;
      if page == Some(p) {
        write!(w, "{n}")
      } else {
        write!(w, "<a href=\"mmtheorems{n}.html\">{n}</a>")
      }?;
      writeln!(
        w,
        "{from}-{to}",
        from = self.pink_num(true, Some(p * THMS_PER_PAGE)),
        to = self.pink_num(false, ((p + 1) * THMS_PER_PAGE).min(end).checked_sub(1)),
      )?;
    }

    writeln!(
      w,
      "<hr>\n\
        <table style=\"white-space: nowrap; width: 100%\"><tr>\n\
          <td style=\"width: 25%\">&nbsp;</td>\n\
          <td style=\"text-align: center; vertical-align: bottom; \
              font-size: x-small; font-family: Arial,sans-serif\">\
            Copyright terms: <a href=\"../copyright.html#pd\">Public domain</a>\
          </td>\n\
          <td style=\"text-align: right; vertical-align: top; width: 25%; \
              font-size: small; font-family: sans-serif\">\
            {prev_next}\
          </td>\n\
        </tr></table>\n\
      </body></html>"
    )
  }

  pub(crate) fn show_extra<W: Write>(&self, w: &mut W, extra: Extra, alt: bool) -> io::Result<()> {
    let db = self.db;
    let label = extra.label();
    writeln!(
      w,
      "<!DOCTYPE html>\n\
      <html lang=\"en-us\"><head>\n\
        <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">\n\
        <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n\
        <style>\n\
        img {{ border: 0; margin-bottom: -4px; }}\n\
        .r {{ font-family: \"Arial Narrow\"; font-size: x-small; }}\n\
        .main {{ \
          text-align: center; border-spacing: 0; background-color: {bgcolor}; \
          margin: auto; \
          border: outset 1px {border_color}; \
        }}\n\
        .main td, .main th {{ border: inset 1px {border_color}; }}\n\
        .main th {{ text-align: center; }}\n\
        .main td {{ text-align: left; }}\n\
        .title {{ font-weight: bold; color: {title_color}; }}\n\
        hr {{ border-style: solid; border-top: 1px; }}\n\
        .ext {{ background-color: {PURPLISH_BIBLIO_COLOR}; }}\n\
        .sbox {{ background-color: {SANDBOX_COLOR}; }}\n\
        </style>\n\
        {css}\n\
        <title>{label} - {title}</title>\n\
        <link rel=\"shortcut icon\" href=\"favicon.ico\" type=\"image/x-icon\">\n\
      </head><body style=\"background-color: #FFFFFF\">\n\
        <table style=\"border-spacing: 0; width: 100%\">\n\
          <tr>\n\
            <td style=\"padding: 0; text-align: left; vertical-align: top; width: 25%\">\n\
              <a href=\"{home_href}\">\n\
                <img src=\"{home_img}\" alt=\"{title_abbr}\" title=\"{title_abbr}\" \
                  height=32 width=32 style=\"vertical-align: top; margin-bottom: 0px\">\n\
              </a>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: center; vertical-align: top\" colspan=2>\n\
              <span class=title style=\"font-size: xx-large\">{title}</span>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: right; vertical-align: top; width: 25%; \
                font-size: x-small; font-family: sans-serif\">\n\
              This is the {this_name} version.<br>\n\
              <a href=\"{other_dir}{label}.html\">Change to {other_name} version</a>\n\
            </td>\n\
          </tr>\n\
        </table>\n\
        <hr>",
      border_color = GRAY_BORDER_COLOR,
      bgcolor = MINT_BACKGROUND_COLOR,
      css = &*self.html_css,
      title = self.html_title,
      title_abbr = self.html_title_abbr,
      home_href = self.html_home_href,
      home_img = self.html_home_img,
      title_color = GREEN_TITLE_COLOR,
      this_name = if alt { "Unicode" } else { "GIF" },
      other_name = if alt { "GIF" } else { "Unicode" },
      other_dir = if alt { self.html_dir } else { self.alt_html_dir }
    )?;

    match extra {
      Extra::Ascii => {
        writeln!(
          w,
          "<div class=title style=\"text-align: center; font-weight: bold\">\
            Symbol to ASCII Correspondence for Text-Only Browsers \
            (in order of appearance in $c and $v statements in the database)\
          </div>\n\
          <p>\
          <table class=main>\n\
            <tr><td><b>Symbol</b></td><td><b>ASCII</b></td></tr>"
        )?;
        let html_defs = if alt { &self.alt_html_defs } else { &self.html_defs };
        let mut used = HashSet::new();
        for stmt in db.statements() {
          if matches!(stmt.statement_type(), StatementType::Constant | StatementType::Variable) {
            for tk in stmt.math_iter().map(|tk| tk.slice) {
              if used.insert(tk) {
                writeln!(
                  w,
                  "<tr><td class=math>{}</td><td><tt>{}</tt></td></tr>",
                  html_defs[tk],
                  html_escape(as_str(tk))
                )?
              }
            }
          }
        }
      }
      Extra::Definitions | Extra::TheoremsAll => {
        let (desc, expr, tdclass, stype) = match extra {
          Extra::Definitions => (
            "List of Syntax, Axioms (<span class=title>ax-</span>) and \
            Definitions (<span class=title>df-</span>)",
            "Expression (see link for any distinct variable requirements)",
            " class=math",
            StatementType::Axiom,
          ),
          Extra::TheoremsAll => ("List of Theorems", "Description", "", StatementType::Provable),
          _ => unreachable!(),
        };
        writeln!(
          w,
          "<table class=main>\n\
            <caption style=\"text-align: center; font-weight: bold\">{desc}</caption>\n\
            <tr><td><b>Ref</b></td><td><b>{expr}</b></td></tr>"
        )?;
        let end = self.statements.len();
        let get_pink = |addr| Some(*self.pink_numbers.get(db.statement_by_address(addr).label())?);
        let mathbox_num = self.mathbox_addr.and_then(get_pink).unwrap_or(end);
        let ext_html_num =
          self.ext_html_addr.and_then(get_pink).unwrap_or(mathbox_num).min(mathbox_num);
        let scope = db.scope_result();
        let (mut first_ext, mut first_mbox) = (false, false);
        let mut bgclass = "";
        for (s, stmt) in self.statements.iter().enumerate() {
          if stmt.statement_type() == stype {
            let write_header = |w: &mut W, bgclass: &str, title: &str| {
              writeln!(
                w,
                "<tr{bgclass}><td colspan=2 style=\"text-align: center\">\
                    The list of syntax, axioms (<span class=title>ax-</span>) and \
                    definitions (<span class=title>df-</span>) for the \
                    <span class=title style=\"font-weight: bold\">{title}</span> starts here\
                  </td></tr>"
              )
            };
            if ext_html_num <= s {
              if mathbox_num <= s {
                if !first_mbox {
                  first_mbox = true;
                  bgclass = " class=sbox";
                  write_header(w, bgclass, "User Mathboxes")?;
                }
              } else if !first_ext {
                first_ext = true;
                bgclass = " class=ext";
                write_header(w, bgclass, self.ext_html_title)?;
              }
            }
            let body = DisplayFn(|f| match extra {
              Extra::Definitions => {
                let fr = scope.get(stmt.label()).unwrap();
                self.oneline_statement(alt, fr).fmt(f)
              }
              Extra::TheoremsAll =>
                f.write_str(&html_escape(as_str(&abbrev_desc(*stmt, 29, true)))),
              _ => unreachable!(),
            });
            writeln!(
              w,
              "<tr{bgclass}>\
                <td><a href=\"{label}.html\">{label}</a>{pink}</td>\
                <td{tdclass}>{body}</td>\
              </tr>",
              label = as_str(stmt.label()),
              pink = self.pink_num(true, Some(s)),
            )?
          }
        }
      }
    }
    writeln!(w, "</table>\n{FOOTER}</body></html>")
  }

  pub(crate) fn show_recent<W: Write>(
    &self, w: &mut W, num_recent: usize, tpl: usize, alt: bool,
  ) -> io::Result<()> {
    let db = self.db;
    let end = self.statements.len();
    let get_pink = |addr| Some(*self.pink_numbers.get(db.statement_by_address(addr).label())?);
    let mathbox_num = self.mathbox_addr.and_then(get_pink).unwrap_or(end);
    let ext_html_num =
      self.ext_html_addr.and_then(get_pink).unwrap_or(mathbox_num).min(mathbox_num);
    let scope = db.scope_result();
    for elem in &self.recent_templates[tpl].0 {
      match elem {
        TemplateElem::Text(s) => w.write_all(s.as_bytes())?,
        TemplateElem::Main => {
          let mut rest = false;
          for &(date, s) in &self.recent[..num_recent] {
            let stmt = self.statements[s];
            let buf = &stmt.segment().segment.buffer;
            let desc = stmt.associated_comment().unwrap().comment_contents();
            let ext = ext_html_num <= s;
            let mboxness = self.mathbox_lookup(&stmt);
            let fr = scope.get(stmt.label()).unwrap();
            let bgclass = DisplayFn(|f| {
              if ext {
                write!(f, " class={}", if s < mathbox_num { "ext" } else { "sbox" })?
              }
              Ok(())
            });
            if rest {
              writeln!(w, "<tr class=sp><td colspan=3>&nbsp;</td></tr>")?;
            }
            rest = true;
            writeln!(
              w,
              "\n\
              <tr id=\"{label}\"{bgclass}>\
                <td style=\"white-space: nowrap\">{date}</td>\
                <td style=\"text-align: center\"><a href=\"{label}.html\">{label}</a>{pink}{dv}</td>\
                <td class=comment style=\"text-align: left\">{comment}</td>\
              </tr>\
              <tr{bgclass}><td colspan=3 style=\"text-align: center\" class=math>{frame}</td></tr>",
              label = as_str(stmt.label()),
              pink = self.pink_num(true, Some(s)),
              dv = if fr.mandatory_dv.is_empty() { "" } else { "*" },
              comment = self.comment(as_str(desc.as_ref(buf)).trim(), alt, ext && mboxness.is_none()),
              frame = self.oneline_statement(alt, fr),
            )?;
          }
        }
        TemplateElem::LastUpdated => {
          use chrono::{offset::Utc, FixedOffset};
          // Metamath website has historically been in Eastern Standard Time
          const EST_TZ: FixedOffset = match FixedOffset::west_opt(5 * 3600) {
            Some(tz) => tz,
            None => panic!(),
          };
          let now = Utc::now().with_timezone(&EST_TZ);
          writeln!(w, "<i>Last updated on {} ET.</i>", now.format("%-d-%b-%Y at %-I:%M %p"))?;
        }
      }
    }
    Ok(())
  }
}

enum TemplateElem<'a> {
  Main,
  LastUpdated,
  Text(&'a str),
}

struct Template<'a>(Vec<TemplateElem<'a>>);

impl<'a> Template<'a> {
  fn parse(mut body: &'a str) -> Self {
    const START: &str = "<!-- #START# -->";
    const END: &str = "<!-- #END# -->";
    const LAST_UPDATED: &str = "<!-- last updated -->";
    let mut out = vec![];
    let mut main = body.find(START).and_then(|n| Some((n + START.len(), body[n..].find(END)? + n)));
    let mut updated = body.find(LAST_UPDATED).map(|i| i + LAST_UPDATED.len());
    loop {
      if let Some((start, end)) = main.filter(|n| !matches!(updated, Some(m) if m < n.0)) {
        out.push(TemplateElem::Text(&body[..start]));
        out.push(TemplateElem::Main);
        body = &body[end..];
        main = body.find(START).and_then(|n| Some((n + START.len(), body[n..].find(END)? + n)));
        updated = updated.map(|e| e - end);
      } else if let Some(end) = updated {
        out.push(TemplateElem::Text(&body[..end]));
        out.push(TemplateElem::LastUpdated);
        body = &body[end..];
        main = main.map(|(s, e)| (s - end, e - end));
        updated = body.find(LAST_UPDATED).map(|i| i + LAST_UPDATED.len());
      } else {
        out.push(TemplateElem::Text(body));
        return Template(out)
      }
    }
  }
}

fn abbrev_desc(stmt: StatementRef<'_>, max_len: usize, break_mid_word: bool) -> Vec<u8> {
  let Some(comment) = stmt.associated_comment() else { return vec![] };
  let span = comment.span();
  let mut comment = &comment.segment().buffer[(span.start + 2) as usize..(span.end - 2) as usize];
  match comment.iter().position(|c| !c.is_ascii_whitespace()) {
    Some(j) => comment = &comment[j..],
    None => return vec![],
  }
  let mut out = vec![];
  let i = comment.iter().position(|c| c.is_ascii_whitespace()).unwrap_or(comment.len());
  let truncated = if i > max_len {
    if break_mid_word {
      out.extend_from_slice(&comment[..i]);
    }
    true
  } else {
    out.extend_from_slice(&comment[..i]);
    comment = &comment[i + 1..];
    loop {
      match comment.iter().position(|c| !c.is_ascii_whitespace()) {
        Some(j) => comment = &comment[j..],
        None => break false,
      }
      let i = comment.iter().position(|c| c.is_ascii_whitespace()).unwrap_or(comment.len());
      if out.len() + i >= max_len {
        if break_mid_word {
          out.push(b' ');
          out.extend_from_slice(&comment[..i]);
        }
        break true
      }
      out.push(b' ');
      out.extend_from_slice(&comment[..i]);
      comment = &comment[i + 1..];
    }
  };
  if truncated {
    if out.len() > max_len - 3 {
      let max = if break_mid_word {
        max_len - 3
      } else {
        out[..=max_len - 3].iter().rposition(|&c| c == b' ').unwrap_or(0)
      };
      out.truncate(max);
    }
    if !out.is_empty() {
      out.extend_from_slice(b"...")
    }
  }
  out
}

struct DisplayFn<F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result>(F);

impl<F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result> Display for DisplayFn<F> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.0(f) }
}

struct CalcOrder<'a> {
  db: &'a Database,
  arr: &'a ProofTreeArray,
  skip_syntax: bool,
  reverse: Box<[u32]>,
  order: Vec<(usize, u16)>,
}

const UNREACHABLE: u32 = 0;
const SKIPPED_STEP: u32 = u32::MAX;
impl<'a> CalcOrder<'a> {
  fn new(db: &'a Database, arr: &'a ProofTreeArray, skip_syntax: bool) -> Self {
    CalcOrder {
      db,
      arr,
      skip_syntax,
      reverse: vec![UNREACHABLE; arr.trees.len()].into(),
      order: vec![],
    }
  }
  fn step(&mut self, i: usize, depth: u16) {
    if self.reverse[i] != 0 {
      return
    }
    let tree = &self.arr.trees[i];
    if self.skip_syntax && *self.db.statement_by_address(tree.address).math_at(0) != *b"|-" {
      self.reverse[i] = SKIPPED_STEP;
      return
    }
    for &child in &tree.children {
      self.step(child, depth + 1);
    }
    self.order.push((i, depth));
    self.reverse[i] = self.order.len() as u32;
  }
}

struct UseIter<'a> {
  stmt: StatementRef<'a>,
  i: i32,
  len: i32,
}

impl<'a> UseIter<'a> {
  fn new(stmt: StatementRef<'a>) -> Self {
    let len = stmt.proof_len();
    if len != 0 && stmt.proof_slice_at(0) == b"(" {
      Self { stmt, i: 1, len }
    } else {
      Self { stmt, i: 0, len }
    }
  }
}

impl<'a> Iterator for UseIter<'a> {
  type Item = &'a [u8];

  fn next(&mut self) -> Option<Self::Item> {
    if self.i >= self.len {
      return None
    }
    let ref_stmt = self.stmt.proof_slice_at(self.i);
    if ref_stmt == b")" {
      return None
    }
    self.i += 1;
    Some(ref_stmt)
  }
}

#[derive(Default)]
struct TraceUsage<'a>(HashMap<&'a [u8], HashSet<&'a [u8]>>);

impl<'a> TraceUsage<'a> {
  fn get(&mut self, db: &'a Database, label: &'a [u8]) -> &HashSet<&'a [u8]> {
    if let Some(val) = self.0.get(label) {
      return unsafe { std::mem::transmute(val) }
    }

    let out = (|| -> Option<_> {
      let mut out = HashSet::new();
      let stmt = db.statement_by_address(db.name_result().lookup_label(label)?.address);
      match stmt.statement_type() {
        StatementType::Axiom => return None,
        StatementType::Provable => {}
        _ => return Some(out),
      }
      for ref_stmt in UseIter::new(stmt) {
        for &ax in self.get(db, ref_stmt) {
          out.insert(ax);
        }
      }
      Some(out)
    })()
    .unwrap_or_else(|| std::iter::once(label).collect());
    self.0.entry(label).or_insert(out)
  }
}

fn is_direct_use(stmt: &StatementRef<'_>, label: &[u8]) -> bool {
  stmt.statement_type() == StatementType::Provable && {
    let len = stmt.proof_len();
    if len == 0 || stmt.proof_slice_at(0) != b"(" {
      return false
    }
    for i in 1..len {
      let ref_stmt = stmt.proof_slice_at(i);
      if ref_stmt == b")" {
        break
      } else if ref_stmt == label {
        return true
      }
    }
    false
  }
}

/// Calculates a clique cover of an undirected graph with vertices in `0..max` and with edges
/// the elements of `edges` connecting two vertices in the graph. The cover is guaranteed to be
/// exact (represents all and only the specified edges), but it is only approximately minimal.
///
/// This is a classic algorithm from Kellerman (1973).
fn approximate_clique_cover(max: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
  if max == 0 || edges.is_empty() {
    return vec![]
  }
  let mut out = vec![vec![0]];
  for i in 1..max {
    let mut neighbors = edges
      .iter()
      .filter_map(|&(a, b)| {
        if a == i {
          Some(b)
        } else if b == i {
          Some(a)
        } else {
          None
        }
      })
      .filter(|&j| j < i)
      .map(|j| (j, false))
      .collect_vec();
    if neighbors.is_empty() {
      out.push(vec![i]);
    } else {
      for cl in &mut out {
        if cl.iter().all(|&x| neighbors.iter().any(|p| p.0 == x)) {
          cl.push(i);
          neighbors.iter_mut().filter(|p| cl.contains(&p.0)).for_each(|p| p.1 = true);
          if neighbors.iter().all(|p| p.1) {
            break
          }
        }
      }
      neighbors.retain(|p| !p.1);
      while !neighbors.is_empty() {
        let cl = out
          .iter()
          .max_by_key(|cl| neighbors.iter().filter(|p| cl.contains(&p.0)).count())
          .unwrap();
        let mut newcl = vec![i];
        newcl.extend(cl.iter().copied().filter(|&i| neighbors.iter().any(|p| p.0 == i)));
        neighbors.retain(|p| !cl.contains(&p.0));
        out.push(newcl)
      }
    }
  }
  out
}

#[test]
fn approximate_clique_cover_test() {
  let max = 10;
  let mut edges = vec![];
  for i in 1..max {
    for j in 0..i {
      if i % (j + 1) == 0 {
        edges.push((i, j));
      }
    }
  }
  println!("cover({max}, {edges:?})");
  // let mut now = Instant::now();
  let mut out = approximate_clique_cover(max, &edges);
  // dur += now.elapsed();
  println!(" = {:?}", out);
  let mut a1 = edges.iter().map(|&(a, b)| (a.min(b), a.max(b))).collect_vec();
  let mut a2 = out
    .iter_mut()
    .flat_map(|cl| {
      cl.sort_unstable();
      (1..cl.len()).flat_map(|i| {
        let b = cl[i];
        cl[..i].iter().map(move |&a| (a, b))
      })
    })
    .collect_vec();
  a1.sort_unstable();
  a2.sort_unstable();
  a2.dedup();
  assert_eq!(a1, a2);
}
