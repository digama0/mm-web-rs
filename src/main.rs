use itertools::Itertools;
use metamath_knife::{
  nameck::{Atom, Nameset},
  parser::{as_str, StatementRef, StatementType},
  proof::ProofTreeArray,
  scopeck::{Frame, Hyp, VerifyExpr},
  *,
};
use std::{
  cell::RefCell,
  collections::{HashMap, HashSet},
  fmt::Display,
  io::{self, Write},
  ops::Bound,
};

const GREEN_TITLE_COLOR: &str = "#006633";
const MINT_BACKGROUND_COLOR: &str = "#EEFFFA";

fn main() {
  let mut db = Database::default();
  db.parse("../mm/set.mm".into(), vec![]);
  db.scope_pass();
  db.typesetting_pass();
  let renderer = Renderer::new(&db);

  let label = "pntleml";
  // let mut w = &mut File::create(format!("{}.html", label)).unwrap();
  let w = &mut std::io::stdout();
  let stmt = db.statement(label.as_bytes()).unwrap();
  renderer.show_statement(w, stmt, true, true).unwrap();
}

struct Renderer<'a> {
  db: &'a Database,
  pink_numbers: HashMap<&'a [u8], usize>,
  // latex_defs: HashMap<&'a [u8], &'a str>,
  html_defs: HashMap<&'a [u8], &'a str>,
  alt_html_defs: HashMap<&'a [u8], &'a str>,
  html_var_color: String,
  html_title: &'a str,
  // html_home: &'a str,
  html_dir: &'a str,
  alt_html_dir: &'a str,
  // html_bibliography: &'a str,
  html_css: String,
  html_font: Option<&'a str>,
  // ext_html_label: &'a str,
  // ext_html_title: &'a str,
  // ext_html_home: &'a str,
  // ext_html_bibliography: &'a str,
  html_ext_url: &'a str,
  title_abbr: String,
  home_href: &'a str,
  home_img: &'a str,
  first_order_tc: Vec<Atom>,
  second_order_tc: Vec<Atom>,
  syntax_hint: HashMap<&'a [u8], Box<[u8]>>,
  trace_usage: RefCell<TraceUsage<'a>>,
}

impl<'a> Renderer<'a> {
  fn new(db: &'a Database) -> Self {
    let pink_numbers = db
      .statements()
      .filter(|s| s.is_assertion())
      .enumerate()
      .map(|(i, l)| (l.label(), i))
      .collect();
    let ts = &**db.typesetting_result();
    let html_title = ts.html_title.as_deref().map_or("Metamath Test Page", as_str);
    let html_home = ts.html_home.as_deref().map_or(
      "<A HREF=\"mmset.html\"><FONT SIZE=-2 FACE=sans-serif>\
        <IMG SRC=\"mm.gif\" BORDER=0 ALT=\"Home\"\
          HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE=\"margin-bottom:0px\">Home</FONT></A>",
      as_str,
    );
    let names = db.name_result();
    let get_tc = |arr: &[&[u8]]| arr.iter().map(|v| names.lookup_symbol(v).unwrap().atom).collect();
    Self {
      db,
      pink_numbers,
      // latex_defs: ts.latex_defs.iter().map(|(x, y)| (&**x, as_str(y))).collect(),
      html_defs: ts.html_defs.iter().map(|(x, y)| (&**x, as_str(y))).collect(),
      alt_html_defs: ts.alt_html_defs.iter().map(|(x, y)| (&**x, as_str(y))).collect(),
      html_var_color: Itertools::intersperse(ts.html_var_color.iter().map(|s| as_str(s)), " ")
        .collect::<String>(),
      html_title,
      // html_home,
      html_dir: ts.html_dir.as_deref().map_or("", as_str),
      alt_html_dir: ts.alt_html_dir.as_deref().map_or("", as_str),
      // html_bibliography: ts.html_bibliography.as_deref().map_or("", as_str),
      html_css: ts.html_css.as_deref().map_or("", as_str).replace("\\n", "\n"),
      html_font: ts.html_font.as_deref().map(as_str),
      // ext_html_label: ts.ext_html_label.as_deref().map_or("", as_str),
      // ext_html_title: ts.ext_html_title.as_deref().map_or("", as_str),
      // ext_html_home: ts.ext_html_home.as_deref().map_or("", as_str),
      // ext_html_bibliography: ts.ext_html_bibliography.as_deref().map_or("", as_str),
      html_ext_url: ts.html_ext_url.as_deref().map_or("", as_str),
      title_abbr: format!(
        "{} Home",
        html_title.matches(|c: char| c.is_ascii_uppercase()).collect::<String>()
      ),
      home_href: html_home.split_once("HREF=\"").unwrap().1.split_once("\"").unwrap().0,
      home_img: html_home.split_once("IMG SRC=\"").unwrap().1.split_once("\"").unwrap().0,
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
        write!(f, "&nbsp;<SPAN CLASS=r STYLE=\"color:#")?;
        for d in 0..3 {
          write!(
            f,
            "{:02X}",
            (SPECTRUM[i][d] as f64 + fraction * (SPECTRUM[i + 1][d] as f64 - SPECTRUM[i][d] as f64))
              .round() as u8
          )?;
        }
        write!(f, "\">{}</SPAN>", n + 1)
      } else {
        write!(f, "&nbsp;<SPAN CLASS=r STYLE=\"color:#000000\">(future)</SPAN>")
      }
    })
  }
}

struct FrameRenderer<'a> {
  names: &'a Nameset,
  html_defs: &'a HashMap<&'a [u8], &'a str>,
  frame: &'a Frame,
  html_span: Option<&'a str>,
}

impl<'a> Renderer<'a> {
  fn frame_renderer(&self, alt: bool, frame: &'a Frame) -> FrameRenderer<'_> {
    FrameRenderer {
      names: self.db.name_result(),
      html_defs: if alt { &self.alt_html_defs } else { &self.html_defs },
      html_span: if alt { self.html_font } else { None },
      frame,
    }
  }
}

impl<'a> FrameRenderer<'a> {
  fn verify_expr(&'a self, e: &'a VerifyExpr) -> impl Display + 'a {
    DisplayFn(|f| {
      if let Some(html_font) = self.html_span {
        write!(f, "<SPAN {}>", html_font)?
      }
      write!(f, "{}", self.get_atom(e.typecode))?;
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
      if self.html_span.is_some() {
        write!(f, "</SPAN>")?
      }
      Ok(())
    })
  }

  fn expr(&'a self, typecode: &'a [u8], e: &'a [u8]) -> impl Display + 'a {
    DisplayFn(|f| {
      if let Some(html_font) = self.html_span {
        write!(f, "<SPAN {}>", html_font)?
      }
      write!(f, "{}", self.html_defs[typecode])?;
      for tk in e.split(|&c| c == b' ').skip(1) {
        write!(f, "{}", self.html_defs[tk])?
      }
      if self.html_span.is_some() {
        write!(f, "</SPAN>")?
      }
      Ok(())
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
    if let Some(html_font) = self.html_span {
      write!(f, "<SPAN {}>", html_font)?
    }
    write!(f, "{}", self.get_atom(self.e.typecode))?;
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
    if self.html_span.is_some() {
      write!(f, "</SPAN>")?
    }
    Ok(())
  }
}

struct ExprHtml<'a> {
  fr: &'a FrameRenderer<'a>,
  e: &'a [u8],
}

impl Display for ExprHtml<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if let Some(html_font) = self.fr.html_span {
      write!(f, "<SPAN {}>", html_font)?
    }
    for tk in self.e.split(|&c| c == b' ') {
      write!(f, "{}", self.fr.html_defs[tk])?
    }
    if self.fr.html_span.is_some() {
      write!(f, "</SPAN>")?
    }
    Ok(())
  }
}

impl<'a> Renderer<'a> {
  #[allow(clippy::too_many_arguments)]
  fn show_statement(
    &self, w: &mut impl Write, stmt: StatementRef<'a>, alt: bool, in_mbox: bool,
  ) -> io::Result<()> {
    let db = self.db;
    let css = &*self.html_css;
    let title = self.html_title;
    let title_abbr = &*self.title_abbr;
    let home_href = self.home_href;
    let home_img = self.home_img;
    let html_ext_url = self.html_ext_url;
    let other_dir = if alt { self.html_dir } else { self.alt_html_dir };

    let sub_type = match stmt.statement_type() {
      StatementType::Provable => ("Theorem", "theorem"),
      _ => unimplemented!(),
    };
    let label = stmt.label();
    let s_label = as_str(label);
    let seg = stmt.segment();
    let span = stmt.associated_comment().unwrap().span();
    let comment = as_str(&seg.buffer[(span.start + 2) as usize..(span.end - 2) as usize])
      .replace("<", "&lt;")
      .replace(">", "&gt;")
      .replace("&", "&amp;");

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
      <HTML LANG=\"EN-US\"><HEAD>\n\
        <META HTTP-EQUIV=\"Content-Type\" CONTENT=\"text/html; charset=iso-8859-1\">\n\
        <meta charset=\"iso-8859-1\">\n\
        <META NAME=\"viewport\" CONTENT=\"width=device-width, initial-scale=1.0\">\n\
        <STYLE TYPE=\"text/css\">\n\
        <!--\n\
        img {{ margin-bottom: -4px }}\n\
        .r {{ font-family: \"Arial Narrow\"; font-size: x-small; }}\n\
        .i {{ font-family: \"Arial Narrow\"; font-size: x-small; color: gray; }}\n\
        -->\n\
        </STYLE>\n\
        {css}\n\
        <TITLE>{label} - {title}</TITLE>\n\
        <LINK REL=\"shortcut icon\" HREF=\"favicon.ico\" TYPE=\"image/x-icon\">\n\
      </HEAD><BODY BGCOLOR=\"#FFFFFF\">\n\
        <TABLE BORDER=0 CELLSPACING=0 CELLPADDING=0 WIDTH=\"100%\">\n\
          <TR>\n\
            <TD ALIGN=LEFT VALIGN=TOP WIDTH=\"25%\">\n\
              <A HREF= \"{home_href}\">\n\
                <IMG SRC=\"{home_img}\" BORDER=0 ALT=\"{title_abbr}\" TITLE=\"{title_abbr}\" \
                  HEIGHT=32 WIDTH=32 ALIGN=TOP STYLE=\"margin-bottom:0px\">\n\
              </A>\n\
            </TD>\n\
            <TD ALIGN=CENTER COLSPAN=2 VALIGN=TOP>\n\
              <FONT SIZE=\"+3\" COLOR=\"{title_color}\">\n\
                <B>{title}</B>\n\
              </FONT>\n\
            </TD><TD ALIGN=RIGHT VALIGN=TOP WIDTH=\"25%\">\n\
              <FONT SIZE=-1 FACE=sans-serif>\n\
                <A HREF=\"{prev}.html\">&lt; {prev_text}</A>&nbsp;&nbsp;\
                <A HREF=\"{next}.html\">{next_text} &gt;</A>\n\
              </FONT><FONT FACE=sans-serif SIZE=-2>\n\
                <BR/><A HREF=\"mmtheorems{page}.html#{label}\">Nearby theorems</A>\n\
              </FONT>\n\
            </TD>\n\
          </TR><TR>\n\
            <TD COLSPAN=2 ALIGN=LEFT VALIGN=TOP>
              <FONT SIZE=-2 FACE=sans-serif>\n\
                <A HREF=\"../mm.html\">Mirrors</A>&nbsp; &gt; &nbsp;\
                <A HREF=\"../index.html\">Home</A>&nbsp; &gt; &nbsp;\
                <A HREF=\"{home_href}\">{title_abbr}</A>&nbsp; &gt; &nbsp;\
                <A HREF=\"mmtheorems.html\">Th. List</A>&nbsp; &gt; &nbsp;\
                {mbox}\
                {label}\
            </FONT>\n\
          </TD><TD COLSPAN=2 ALIGN=RIGHT VALIGN=TOP>\n\
            <FONT SIZE=-2 FACE=sans-serif>\n\
                {html_ext_url}\
                <A HREF=\"{other_dir}{label}.html\">{other_name} version</A>\n\
              </FONT>\n\
            </TD>\n\
          </TR>\n\
        </TABLE>\n\
        <HR NOSHADE SIZE=1/>\n\
        <CENTER>\n\
          <B><FONT SIZE=\"+1\">{sub_type} <FONT COLOR=\"{title_color}\">{label}</FONT></FONT></B>
          {pink_html}
        </CENTER>\n\
        <CENTER><TABLE><TR><TD ALIGN=LEFT>\
          <B>Description: </B>{comment}\
        </TD></TR></TABLE></CENTER>",
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
      mbox = if in_mbox {
        "<A HREF=\"mmtheorems.html#sandbox:bighdr\">Mathboxes</A>&nbsp; &gt; &nbsp;"
      } else {
        ""
      },
      html_ext_url = html_ext_url.replace("*", s_label),
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
        "<CENTER>\n\
        <TABLE BORDER CELLSPACING=0 BGCOLOR=\"{bgcolor}\" SUMMARY=\"Hypothes{es}\">\n\
          <CAPTION><B>Hypothes{es}</B></CAPTION>\n\
          <TR><TH>Ref</TH><TH>Expression</TH></TR>",
        bgcolor = MINT_BACKGROUND_COLOR,
        es = if num_hyps == 1 { "is" } else { "es" },
      )?;
      for hyp in &*fr.hypotheses {
        if let Hyp::Essential(s, ref e) = *hyp {
          let s = db.statement_by_address(s);
          writeln!(
            w,
            "<TR ALIGN=LEFT><TD>{label}</TD><TD>{fmla}</TD></TR>",
            label = as_str(s.label()),
            fmla = frr.verify_expr(e),
          )?
        }
      }
      writeln!(w, "</TABLE></CENTER>")?;
    }
    writeln!(
      w,
      "<CENTER><TABLE BORDER CELLSPACING=0 BGCOLOR=\"{bgcolor}\" SUMMARY=\"Assertion\">\n\
        <CAPTION><B>Assertion</B></CAPTION>\n\
        <TR><TH>Ref</TH><TH>Expression</TH></TR>\n\
        <TR ALIGN=LEFT>\n\
          <TD><FONT COLOR=\"{title_color}\"><B>{label}</B></FONT></TD>\n\
          <TD>{expr}</TD>\n\
        </TR>
      </TABLE></CENTER>",
      bgcolor = MINT_BACKGROUND_COLOR,
      title_color = GREEN_TITLE_COLOR,
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
        "<CENTER><A HREF=\"/mpeuni/mmset.html#distinct\">Distinct variable</A> group{s}: ",
        s = if dvs.len() == 1 { "" } else { "s" },
      )?;
      if let Some(html_font) = frr.html_span {
        write!(w, "<SPAN {}>", html_font)?
      }
      for cl in dvs {
        write!(w, " &nbsp; {}", cl.iter().map(|&v| frr.html_defs[names[v].as_bytes()]).format(","))?
      }
      if frr.html_span.is_some() {
        write!(w, "</SPAN>")?
      }
      writeln!(w, "</CENTER>")?;

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
        "<CENTER><A HREF=\"/mpeuni/mmset.html#allowedsubst\">Allowed substitution</A> hint{s}: ",
        s = if count == 1 { "" } else { "s" },
      )?;
      if let Some(html_font) = frr.html_span {
        write!(w, "<SPAN {}>", html_font)?
      }
      write!(w, "{}", output)?;
      if frr.html_span.is_some() {
        write!(w, "</SPAN>")?
      }
    }
    writeln!(w, "<HR NOSHADE SIZE=1>")?;

    let mut dummies = (fr.mandatory_count..fr.optional_dv.len())
      .filter(|&i| !fr.optional_dv[i].is_empty())
      .collect::<Vec<_>>();
    let thm_header = format!(
      "<B>Proof of Theorem <FONT COLOR=\"{title_color}\">{label}</FONT></B>",
      title_color = GREEN_TITLE_COLOR,
      label = s_label,
    );
    let table_header = format!(
      "<CENTER><TABLE BORDER CELLSPACING=0 BGCOLOR=\"{bgcolor}\" SUMMARY=\"Proof of theorem\">",
      bgcolor = MINT_BACKGROUND_COLOR
    );
    if !dummies.is_empty() {
      dummies.sort_by_key(|&i| names[i]);
      writeln!(w, "<CENTER>{}</CENTER>\n", thm_header)?;
      writeln!(
        w,
        "<CENTER><A HREF=\"/mpeuni/mmset.html#dvnote1\">Dummy variable{s}</A> ",
        s = if dummies.len() == 1 { "" } else { "s" },
      )?;
      if let Some(html_font) = frr.html_span {
        write!(w, "<SPAN {}>", html_font)?
      }
      write!(w, "{}", dummies.iter().map(|&v| frr.html_defs[names[v].as_bytes()]).format(" "))?;
      if frr.html_span.is_some() {
        write!(w, "</SPAN>")?
      }
      writeln!(
        w,
        " {is} distinct from all other variables.</CENTER>",
        is = if dummies.len() == 1 { "is" } else { "are mutually distinct and" },
      )?;
      writeln!(w, "{}", table_header)?
    } else {
      writeln!(w, "{}\n<CAPTION>{}</CAPTION>", table_header, thm_header)?;
    }
    writeln!(w, "<TR><TH>Step</TH><TH>Hyp</TH><TH>Ref</TH><TH>Expression</TH></TR>")?;

    let mut syntax = vec![];
    if let Some(proof) = db.get_proof_tree(stmt) {
      let mut order = CalcOrder::new(db, &proof);
      order.step(proof.qed);
      let indent = proof.indent();
      for (step, &i) in order.order.iter().enumerate() {
        let tree = &proof.trees[i];
        let expr = &*proof.exprs[i];
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
              iter.map(|i| DisplayFn(move |f| write!(f, "<A HREF=\"#{i}\">{i}</A>", i = i)));
            write!(f, "{}", iter.format(", "))
          } else {
            write!(f, "&nbsp;")
          }
        });

        writeln!(w, "<TR ALIGN=LEFT><TD>{}</TD>\n<TD>{}</TD>", step + 1, hyp)?;
        if ref_stmt.is_assertion() {
          writeln!(
            w,
            "<TD><A HREF=\"{ref_label}.html\" TITLE=\"{descr}\">{ref_label}</A>{pink}</TD>",
            ref_label = as_str(ref_stmt.label()),
            descr = as_str(&abbrev_desc(ref_stmt)).replace("\"", "'"),
            pink = self.pink_num(Some(self.pink_numbers[ref_stmt.label()])),
          )?;
        } else {
          writeln!(w, "<TD>{}</TD>", as_str(ref_stmt.label()))?;
        }
        write!(w, "<TD><SPAN CLASS=i>")?;
        (0..indent[i]).try_for_each(|_| write!(w, ". "))?;
        writeln!(
          w,
          "{indent}</SPAN>\n{fmla}</TD></TR>",
          indent = indent[i],
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
        "<TR ALIGN=LEFT><TD COLSPAN=4><B>\
            <FONT COLOR=RED>WARNING: Proof has a severe error.</FONT>\
          </B></TD></TR>"
      )?
    }
    writeln!(w, "</TABLE></CENTER>")?;

    writeln!(w, "<CENTER><TABLE CELLSPACING=5>")?;
    writeln!(
      w,
      "<TR><TD ALIGN=LEFT>\
          <FONT SIZE=-1><B>Colors of variables:</B> {var_color}</FONT>\
        </TD></TR>",
      var_color = self.html_var_color,
    )?;

    if !syntax.is_empty() {
      syntax.sort_by_key(|(stmt, _)| self.pink_numbers[stmt]);
      write!(w, "<TR><TD ALIGN=LEFT><FONT SIZE=-1><B>Syntax hints:</B> ")?;
      for (label, c) in syntax {
        write!(w, " &nbsp;")?;
        if let Some(html_font) = frr.html_span {
          write!(w, "<SPAN {}>", html_font)?
        }
        write!(w, "{}", frr.html_defs[&**c])?;
        if frr.html_span.is_some() {
          write!(w, "</SPAN>")?
        }
        write!(
          w,
          "<A HREF=\"{label}.html\">{label}</A>{pink}",
          pink = self.pink_num(Some(self.pink_numbers[label])),
          label = as_str(label)
        )?;
      }
      writeln!(w, "</FONT></TD></TR>")?;
    }

    let mut usage = self
      .trace_usage
      .borrow_mut()
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
        writeln!(w, "<TR><TD ALIGN=LEFT><FONT SIZE=-1><B>{}:</B>", header)?;
        for label in labels {
          writeln!(
            w,
            "&nbsp;<A HREF=\"{label}.html\">{label}</A>{pink}",
            label = label,
            pink = self.pink_num(Some(self.pink_numbers[label.as_bytes()])),
          )?
        }
        writeln!(w, "</FONT></TD></TR>")?;
      }
      Ok(())
    };
    write_list("This theorem was proved from axioms", axioms)?;
    write_list("This theorem depends on definitions", defs)?;

    if !usage.is_empty() {
      if matches!(*usage, [stmt] if stmt.label() == label) {
        writeln!(
          w,
          "<TR><TD ALIGN=left>&nbsp;<B><FONT COLOR=\"#FF6600\">\
            WARNING: This theorem has an incomplete proof.</FONT></B><BR></TD></TR>"
        )?
      } else {
        writeln!(
          w,
          "<TR><TD ALIGN=left>&nbsp;<B><FONT COLOR=\"#FF6600\">\
            WARNING: This proof depends on the following unproved theorem(s): "
        )?;
        for stmt in usage {
          writeln!(w, " <A HREF=\"{label}.html\">{label}</A>", label = as_str(stmt.label()))?
        }
        writeln!(w, "</B></FONT></TD></TR>")?;
      }
    }

    let mut iter = db
      .statements_range_address((Bound::Excluded(stmt.address()), Bound::Unbounded))
      .filter(|s| is_direct_use(s, label))
      .peekable();
    writeln!(w, "<TR><TD ALIGN=LEFT><FONT SIZE=-1><B>This {} is referenced by:</B>", sub_type.1)?;
    if iter.peek().is_some() {
      for label in iter.map(|stmt| stmt.label()) {
        writeln!(
          w,
          "&nbsp;<A HREF=\"{label}.html\">{label}</A>{pink}",
          label = as_str(label),
          pink = self.pink_num(Some(self.pink_numbers[label])),
        )?
      }
    } else {
      writeln!(w, " (None)")?
    }
    writeln!(w, "</FONT></TD></TR>")?;
    writeln!(w, "</TABLE></CENTER>")?;

    writeln!(
      w,
      "<TABLE BORDER=0 WIDTH=\"100%\"><TR>\n\
        <TD WIDTH=\"25%\">&nbsp;</TD>\n\
        <TD ALIGN=CENTER VALIGN=BOTTOM>\n\
          <FONT SIZE=-2 FACE=sans-serif>\
            Copyright terms: <A HREF=\"../copyright.html#pd\">Public domain</A>\n\
          </FONT>\
        </TD><TD ALIGN=RIGHT VALIGN=BOTTOM WIDTH=\"25%\">\n\
          <FONT SIZE=-2 FACE=sans-serif>\
            <A HREF=\"http://validator.w3.org/check?uri=referer\">W3C validator</A>\
          </FONT>\n\
        </TD></TR></TABLE>"
    )?;
    writeln!(w, "</BODY></HTML>")
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
      let len = stmt.proof_len();
      if len == 0 || stmt.proof_slice_at(0) != b"(" {
        return None
      }
      for i in 1..len {
        let ref_stmt = stmt.proof_slice_at(i);
        if ref_stmt == b")" {
          return Some(out)
        }
        for &ax in self.get(db, ref_stmt) {
          out.insert(ax);
        }
      }
      None
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
