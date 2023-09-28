use itertools::Itertools;
use metamath_knife::{
  comment_parser::{CommentItem, CommentParser},
  nameck::{Atom, Nameset},
  parser::HeadingLevel,
  proof::ProofTreeArray,
  scopeck::{Frame, Hyp, VerifyExpr},
  statement::StatementAddress,
  *,
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Display,
  io::{self, Write},
  ops::Bound,
  sync::Mutex,
};

const GREEN_TITLE_COLOR: &str = "#006633";
const GRAY_BORDER_COLOR: &str = "#B2B2B2";
const MINT_BACKGROUND_COLOR: &str = "#EEFFFA";

pub(crate) struct Renderer<'a> {
  db: &'a Database,
  pink_numbers: HashMap<&'a [u8], usize>,
  mathbox_addr: Option<StatementAddress>,
  mathbox_lookup: Option<Vec<(StatementAddress, &'a str)>>,
  // latex_defs: HashMap<&'a [u8], &'a str>,
  html_defs: HashMap<&'a [u8], &'a str>,
  alt_html_defs: HashMap<&'a [u8], &'a str>,
  html_var_color: String,
  html_title: &'a str,
  html_title_abbr: String,
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
      "<A HREF=\"mmset.html\"><FONT SIZE=-2 FACE=sans-serif>\
        <IMG SRC=\"mm.gif\" BORDER=0 ALT=\"Home\"\
          HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE=\"margin-bottom:0px\">Home</FONT></A>",
      |s| as_str(&s.1),
    );
    let names = db.name_result();
    let get_tc = |arr: &[&[u8]]| arr.iter().map(|v| names.lookup_symbol(v).unwrap().atom).collect();
    let mathbox_addr = names.lookup_label(b"mathbox").map(|l| l.address);
    let ext_html_title = ts.ext_html_title.as_ref().map_or("", |s| as_str(&s.1));
    let ext_html_home = ts.ext_html_home.as_ref().map_or("", |s| as_str(&s.1));
    let ext_html_home_href =
      ext_html_home.split_once("HREF=\"").unwrap().1.split_once('\"').unwrap().0;
    let ext_html_home_img =
      ext_html_home.split_once("IMG SRC=\"").unwrap().1.split_once('\"').unwrap().0;
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
        "{} Home",
        html_title.matches(|c: char| c.is_ascii_uppercase()).collect::<String>()
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
        "{} Home",
        html_title.matches(|c: char| c.is_ascii_uppercase()).collect::<String>()
      ),
      ext_html_home_href,
      ext_html_home_img,
      ext_html_bibliography: ts.ext_html_bibliography.as_ref().map_or("", |s| as_str(&s.1)),
      html_ext_url: ts.html_ext_url.as_ref().map_or("", |s| as_str(&s.1)),
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
    }
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
  fn pink_num(&self, pink_num: Option<usize>) -> impl Display {
    let max = self.pink_numbers.len() as f64;
    DisplayFn(move |f| {
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
        write!(f, "&nbsp;<span class=r style=\"color:#")?;
        for d in 0..3 {
          write!(
            f,
            "{:02X}",
            (SPECTRUM[i][d] as f64 + fraction * (SPECTRUM[i + 1][d] as f64 - SPECTRUM[i][d] as f64))
              .round() as u8
          )?;
        }
        write!(f, "\">{}</span>", n + 1)
      } else {
        write!(f, "&nbsp;<span class=r style=\"color:#000000\">(future)</span>")
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
  buf: &'a [u8],
  span: Span,
  r: &'b Renderer<'a>,
  html_defs: &'b HashMap<&'a [u8], &'a str>,
  html_bibliography: &'a str,
}

impl<'a> Renderer<'a> {
  fn comment(&self, buf: &'a [u8], span: Span, alt: bool, ext: bool) -> Comment<'a, '_> {
    Comment {
      buf,
      span,
      r: self,
      html_defs: if alt { &self.alt_html_defs } else { &self.html_defs },
      html_bibliography: if ext { self.ext_html_bibliography } else { self.html_bibliography },
    }
  }
}

impl Display for Comment<'_, '_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut parser = CommentParser::new(self.buf, self.span);
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
            write!(f, "{}", s)?
          } else {
            write!(f, "{}", s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;"))?
          }
        }
        CommentItem::LineBreak(_) => {
          trim_prev_ws = true;
          write!(f, "<p style=\"margin-bottom:0em\">")?
        }
        CommentItem::StartMathMode(_) => write!(f, "<span {}>", self.r.html_font)?,
        CommentItem::EndMathMode(_) => {
          trim_prev_ws = true;
          write!(f, "</span>")?
        }
        CommentItem::MathToken(sp) => {
          out.clear();
          parser.unescape_math(sp, &mut out);
          write!(f, "{}", self.html_defs[&*out])?
        }
        CommentItem::Label(_, sp) => {
          trim_prev_ws = true;
          out.clear();
          parser.unescape_label(sp, &mut out);
          write!(
            f,
            "<a href=\"{label}.html\">{label}</a>{pink}",
            label = as_str(&out),
            pink = self.r.pink_num(Some(self.r.pink_numbers[&*out])),
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
        CommentItem::EndItalic(_) => {
          trim_prev_ws = true;
          write!(f, "</i>")?
        }
        CommentItem::BibTag(sp) => {
          trim_prev_ws = false;
          write!(
            f,
            "[<a href=\"{file}#{tag}\">{tag}</a>]",
            file = self.html_bibliography,
            tag = as_str(sp.as_ref(self.buf))
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
  #[allow(clippy::too_many_arguments)]
  pub(crate) fn show_statement(
    &self, w: &mut impl Write, stmt: StatementRef<'a>, alt: bool,
  ) -> io::Result<()> {
    let db = self.db;
    let css = &*self.html_css;
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

    let sub_type = match stmt.statement_type() {
      StatementType::Provable => ("Theorem", "theorem"),
      _ => unimplemented!(),
    };
    let label = stmt.label();
    let s_label = as_str(label);
    let seg = stmt.segment().segment;
    let comment = self.comment(
      &seg.buffer,
      stmt.associated_comment().unwrap().comment_contents(),
      alt,
      ext && mboxness.is_none(),
    );

    let cur = db.name_result().lookup_label(label).unwrap().address;
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
        <!--\n\
        img {{ border: 0; margin-bottom: -4px }}\n\
        .steps {{ \
          text-align: center; border-spacing: 0; background-color: {bgcolor}; \
          margin-left: auto; margin-right: auto; \
          border: outset 1px {border_color}; \
        }}\n\
        .steps td, .steps th {{ border: inset 1px {border_color}; }}\n\
        .steps th {{ text-align: center; }}\n\
        .steps td {{ text-align: left; }}\n\
        .title {{ font-weight: bold; color: {title_color}; }}\n\
        .bottom-table {{ \
          text-align: center; border-spacing: 5px; \
          margin-left: auto; margin-right: auto; \
        }}\n\
        .bottom-table td {{ text-align: left; font-size: small; }}\n\
        hr {{ border-style: solid; border-top: 1px; }}\n\
        .r {{ font-family: \"Arial Narrow\"; font-size: x-small; }}\n\
        .i {{ font-family: \"Arial Narrow\"; font-size: x-small; color: gray; }}\n\
        -->\n\
        </style>\n\
        {css}\n\
        <title>{label} - {title}</title>\n\
        <link rel=\"shortcut icon\" href=\"favicon.ico\" type=\"image/x-icon\">\n\
      </head><body style=\"background-color: #FFFFFF\">\n\
        <table style=\"border-width: 0; border-spacing: 0; width: 100%\">\n\
          <tr>\n\
            <td style=\"padding: 0; text-align: left; vertical-align: top; width: 25%\">\n\
              <a href=\"{home_href}\">\n\
                <img src=\"{home_img}\" alt=\"{title_abbr}\" title=\"{title_abbr}\" \
                  height=32 width=32 style=\"vertical-align: top; margin-bottom: 0px\">\n\
              </a>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: center; vertical-align: top\" colspan=2>\n\
              <b style=\"font-size: xx-large; color: {title_color}\">{title}</b>\n\
            </td>\n\
            <td style=\"padding: 0; text-align: right; vertical-align: top; width: 25%; \
                font-size: x-small; font-family: sans-serif\">\n\
              <span style=\"font-size: small\">\n\
                <a href=\"{prev}.html\">&lt; {prev_text}</a>&nbsp;&nbsp;\n\
                <a href=\"{next}.html\">{next_text} &gt;</a>\n\
              </span><br/>\
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
        <hr />\n\
        <div style=\"text-align: center\">\n\
          <b style=\"font-size: large\">\
            {sub_type} <span class=title>{label}</span>\
          </b>{pink_html}\
        </div>\n\
        <div style=\"text-align: center; padding: 3px\">\n\
          <div style=\"text-align: left; display: inline-block\">\
            <b>Description: </b>{comment}\
          </div>\n\
        </div>",
      border_color = GRAY_BORDER_COLOR,
      bgcolor = MINT_BACKGROUND_COLOR,
      css = css,
      label = s_label,
      title = title,
      home_href = home_href,
      home_img = home_img,
      title_abbr = title_abbr,
      title_color = GREEN_TITLE_COLOR,
      prev = as_str(prev.label()),
      prev_text = if wrap_prev { "Wrap" } else { "Previous" },
      next = as_str(next.label()),
      next_text = if wrap_next { "Wrap" } else { "Next" },
      page = self.pink_numbers[stmt.label()] / 100 + 1,
      mbox = if mboxness.is_some() {
        "<a href=\"mmtheorems.html#sandbox:bighdr\">Mathboxes</a>&nbsp; &gt; &nbsp;"
      } else {
        ""
      },
      html_ext_url = html_ext_url.replace('*', s_label),
      other_name = if alt { "GIF" } else { "Unicode" },
      other_dir = other_dir,
      sub_type = sub_type.0,
      pink_html = self.pink_num(Some(self.pink_numbers[stmt.label()])),
      comment = comment,
    )?;

    let fr = db.scope_result().get(stmt.label()).unwrap();
    let frr = self.frame_renderer(alt, fr);
    let num_hyps = fr.hypotheses.iter().filter(|h| matches!(h, Hyp::Essential(..))).count();
    if num_hyps != 0 {
      writeln!(
        w,
        "<table class=steps>\n\
          <caption><b>Hypothes{es}</b></caption>\n\
          <tr><th>Ref</th><th>Expression</th></tr>",
        es = if num_hyps == 1 { "is" } else { "es" },
      )?;
      for hyp in &*fr.hypotheses {
        if let Hyp::Essential(s, ref e) = *hyp {
          let s = db.statement_by_address(s);
          writeln!(
            w,
            "<tr><td>{label}</td><td class=math>{fmla}</td></tr>",
            label = as_str(s.label()),
            fmla = frr.verify_expr(e),
          )?
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
      write!(
        w,
        "<div style=\"text-align: center\">\
          <a href=\"/mpeuni/mmset.html#allowedsubst\">Allowed substitution</a> hint{s}: ",
        s = if count == 1 { "" } else { "s" },
      )?;
      write!(w, "<span class=math>")?;
      write!(w, "{}</span></div>", output)?;
    }
    writeln!(w, "<hr />")?;

    let thm_header = format!("<b>Proof of Theorem <span class=title>{}</span></b>", s_label);
    let mut dummies =
      if (fr.mandatory_count..fr.optional_dv.len()).all(|i| fr.optional_dv[i].is_empty()) {
        vec![]
      } else {
        let vars = UseIter::new(stmt)
          .filter_map(|s| db.scope_result().get(s))
          .filter(|fr| fr.stype == StatementType::Floating)
          .map(|fr| fr.var_list[0])
          .collect::<HashSet<_>>();
        (fr.mandatory_count..fr.optional_dv.len())
          .filter(|&i| !fr.optional_dv[i].is_empty() && vars.contains(&fr.var_list[i]))
          .collect::<Vec<_>>()
      };
    if !dummies.is_empty() {
      dummies.sort_by_key(|&i| names[i]);
      writeln!(w, "<div style=\"text-align: center\">{}</div>\n", thm_header)?;
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
      writeln!(w, "<table class=steps>\n<caption>{}</caption>", thm_header)?;
    }
    writeln!(w, "<tr><th>Step</th><th>Hyp</th><th>Ref</th><th>Expression</th></tr>")?;

    let mut syntax = vec![];
    if let Some(proof) = db.get_proof_tree(stmt) {
      let mut order = CalcOrder::new(db, &proof);
      order.step(proof.qed);
      let indent = proof.indent();
      for (step, &i) in order.order.iter().enumerate() {
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
            let iter =
              iter.map(|i| DisplayFn(move |f| write!(f, "<a href=\"#{i}\">{i}</A>", i = i)));
            write!(f, "{}", iter.format(", "))
          } else {
            write!(f, "&nbsp;")
          }
        });

        writeln!(w, "<tr><td>{}</td>\n<td>{}</td>", step + 1, hyp)?;
        if ref_stmt.is_assertion() {
          writeln!(
            w,
            "<td><a href=\"{ref_label}.html\" title=\"{descr}\">{ref_label}</a>{pink}</td>",
            ref_label = as_str(ref_stmt.label()),
            descr = as_str(&abbrev_desc(ref_stmt)).replace('\"', "'"),
            pink = self.pink_num(Some(self.pink_numbers[ref_stmt.label()])),
          )?;
        } else {
          writeln!(w, "<td>{}</td>", as_str(ref_stmt.label()))?;
        }
        write!(w, "<td class=math><span class=i>")?;
        (0..indent[i]).try_for_each(|_| write!(w, ". "))?;
        writeln!(
          w,
          "{indent}</span>\n{fmla}</td></tr>",
          indent = indent[i] + 1,
          fmla = frr.expr(&ref_stmt.math_at(0), expr)
        )?
      }

      syntax = proof
        .trees
        .iter()
        .map(|tree| tree.address)
        .collect::<HashSet<_>>()
        .into_iter()
        .map(|addr| db.statement_by_address(addr))
        .filter_map(|stmt| self.syntax_hint.get(stmt.label()).map(|c| (stmt.label(), c)))
        .collect_vec()
    } else {
      writeln!(
        w,
        "<tr><td colspan=4 style=\"color: red\"><b>\
            WARNING: Proof has a severe error.\
          </b></td></tr>"
      )?
    }
    writeln!(w, "</table>")?;

    writeln!(
      w,
      "<table class=bottom-table>\n\
        <tr><td><b>Colors of variables:</b> {var_color}</td></tr>",
      var_color = self.html_var_color,
    )?;

    if !syntax.is_empty() {
      syntax.sort_by_key(|(stmt, _)| self.pink_numbers[stmt]);
      write!(w, "<tr><td><b>Syntax hints:</b> ")?;
      for (label, c) in syntax {
        write!(
          w,
          " &nbsp;<span class=math>{tk}</span><A HREF=\"{label}.html\">{label}</A>{pink}",
          tk = frr.html_defs[&**c],
          pink = self.pink_num(Some(self.pink_numbers[label])),
          label = as_str(label)
        )?;
      }
      writeln!(w, "</td></tr>")?;
    }

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
        writeln!(w, "<tr><td><b>{}:</b>", header)?;
        for label in labels {
          writeln!(
            w,
            "&nbsp;<A HREF=\"{label}.html\">{label}</A>{pink}",
            label = label,
            pink = self.pink_num(Some(self.pink_numbers[label.as_bytes()])),
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
            WARNING: This theorem has an incomplete proof.</b><br/></td></tr>"
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

    let mut iter = db
      .statements_range_address((Bound::Excluded(stmt.address()), Bound::Unbounded))
      .filter(|s| is_direct_use(s, label))
      .peekable();
    writeln!(w, "<tr><td><b>This {} is referenced by:</b>", sub_type.1)?;
    if iter.peek().is_some() {
      for label in iter.map(|stmt| stmt.label()) {
        writeln!(
          w,
          "&nbsp;<a href=\"{label}.html\">{label}</a>{pink}",
          label = as_str(label),
          pink = self.pink_num(Some(self.pink_numbers[label])),
        )?
      }
    } else {
      writeln!(w, " (None)")?
    }
    writeln!(w, "</td></tr>")?;
    writeln!(w, "</table>")?;

    writeln!(
      w,
      "<table style=\"border: none; width: 100%\"><tr>\n\
        <td style=\"width: 25%\">&nbsp;</td>\n\
        <td style=\"text-align: center; vertical-align: bottom; \
          font-size: x-small; font-family: sans-serif\">\
          Copyright terms: <a href=\"../copyright.html#pd\">Public domain</a>\n\
        </td>\n\
        <td style=\"text-align: right; vertical-align: bottom; \
          width: 25%; font-size: x-small; font-family: sans-serif\">\
          <a href=\"http://validator.w3.org/check?uri=referer\">W3C validator</a>\
        </td>\n\
      </tr></table>"
    )?;
    writeln!(w, "</body></html>")
  }
}

fn abbrev_desc(stmt: StatementRef<'_>) -> Vec<u8> {
  const MAX_DESCR_LEN: usize = 87;
  let comment = match stmt.associated_comment() {
    Some(comment) => comment,
    None => return vec![],
  };
  let span = comment.span();
  let mut comment = &comment.segment().buffer[(span.start + 2) as usize..(span.end - 2) as usize];
  let mut out = vec![];
  let truncated = loop {
    match comment.iter().position(|c| !c.is_ascii_whitespace()) {
      Some(j) => comment = &comment[j..],
      None => break false,
    }
    let i = comment.iter().position(|c| c.is_ascii_whitespace()).unwrap_or(comment.len());
    if out.len() + i >= MAX_DESCR_LEN {
      break true
    }
    out.push(b' ');
    out.extend_from_slice(&comment[..i]);
    comment = &comment[i + 1..];
  };
  if truncated {
    if out.len() > MAX_DESCR_LEN - 3 {
      let max = out[..=MAX_DESCR_LEN - 3].iter().rposition(|&c| c == b' ').unwrap_or(0);
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
  reverse: Box<[u32]>,
  order: Vec<usize>,
}

const UNREACHABLE: u32 = 0;
const SKIPPED_STEP: u32 = u32::MAX;
impl<'a> CalcOrder<'a> {
  fn new(db: &'a Database, arr: &'a ProofTreeArray) -> Self {
    CalcOrder { db, arr, reverse: vec![UNREACHABLE; arr.trees.len()].into(), order: vec![] }
  }
  fn step(&mut self, i: usize) {
    if self.reverse[i] != 0 {
      return
    }
    let tree = &self.arr.trees[i];
    if *self.db.statement_by_address(tree.address).math_at(0) != *b"|-" {
      self.reverse[i] = SKIPPED_STEP;
      return
    }
    for &child in &tree.children {
      self.step(child);
    }
    self.order.push(i);
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
    .unwrap_or_else(|| [label].into_iter().collect());
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
  println!("cover({}, {:?})", max, &edges);
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
