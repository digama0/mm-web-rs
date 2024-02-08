mod render;

use metamath_rs::{as_str, database::DbOptions, Database, StatementType};
use rayon::prelude::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use render::Renderer;
use std::{
  fs::File,
  io::BufWriter,
  str::FromStr,
  sync::{atomic::AtomicU32, RwLock},
  time::Instant,
};

fn new_db(file: String) -> Database {
  let mut db = Database::new(DbOptions { incremental: true, ..DbOptions::default() });
  db.parse(file.clone(), vec![]);
  assert!(
    db.statements().next().unwrap().statement_type() != StatementType::Eof,
    "file {file} empty or not found"
  );
  db.scope_pass();
  db.typesetting_pass();
  db
}

const THMS_PER_PAGE: usize = 100;

enum Extra {
  Ascii,
  Definitions,
  TheoremsAll,
}
impl Extra {
  fn label(&self) -> &'static str {
    match self {
      Extra::Ascii => "mmascii",
      Extra::Definitions => "mmdefinitions",
      Extra::TheoremsAll => "mmtheoremsall",
    }
  }
}

impl FromStr for Extra {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "mmascii" => Ok(Extra::Ascii),
      "mmdefinitions" => Ok(Extra::Definitions),
      "mmtheoremsall" => Ok(Extra::TheoremsAll),
      _ => Err(()),
    }
  }
}

fn main() {
  // simple_logger::SimpleLogger::new().init().unwrap();
  enum Cmd {
    Stmt(String),
    StmtAll,
    Thms(usize),
    ThmsAll,
    Extra(Extra),
    ExtraAll,
    Recent { n: usize, in_: usize, out_: String },
  }
  let mut iter = std::env::args().skip(1);
  let mut recents = vec![];
  let label = match iter.next().as_deref() {
    Some("write") => {
      let file = iter.next().unwrap();
      let mut cmds = vec![];
      while let Some(arg) = iter.next() {
        let alt = match &*arg {
          "gif" => false,
          "uni" => true,
          _ => panic!("expected 'gif' or 'uni'"),
        };
        let cmd = match &*iter.next().unwrap() {
          "stmt" => {
            let s = iter.next().unwrap();
            match &*s {
              "*" => Cmd::StmtAll,
              _ => Cmd::Stmt(s),
            }
          }
          "thms" => {
            let page = iter.next().unwrap();
            match &*page {
              "*" => Cmd::ThmsAll,
              _ => Cmd::Thms(page.parse().expect("expected integer or '*'")),
            }
          }
          "extra" => {
            let page = iter.next().unwrap();
            if page == "*" {
              Cmd::ExtraAll
            } else {
              Cmd::Extra(
                page.parse().expect("expected 'mmascii', 'mmdefinitions', 'mmtheoremsall', or '*'"),
              )
            }
          }
          "recent" => {
            let n = iter.next().unwrap().parse().expect("expected integer");
            let in_ = iter.next().unwrap();
            let in_ = recents.iter().position(|x| in_ == *x).unwrap_or_else(|| {
              let n = recents.len();
              recents.push(in_);
              n
            });
            Cmd::Recent { n, in_, out_: iter.next().unwrap() }
          }
          _ => panic!("expected 'stmt' or 'thms'"),
        };
        cmds.push((alt, cmd))
      }
      Some((file, cmds))
    }
    Some("server") => None,
    _ => panic!(
      "use 'mm-web-rs write <DB> (<gif|uni> <stmt <LABEL|*> | thms <N|*> | recent N IN OUT>) ...' \
       or 'mm-web-rs server (<ROUTE> <DB>)...'"
    ),
  };

  if let Some((file, cmds)) = label {
    let mut db = new_db(file);
    if cmds.iter().any(|(_, cmd)| match cmd {
      Cmd::StmtAll => true,
      Cmd::Stmt(label) =>
        db.statement(label.as_bytes()).unwrap().statement_type() == StatementType::Axiom,
      _ => false,
    }) {
      db.grammar_pass();
    }

    let mut renderer = Renderer::new(&db);
    let recent_buffers: Vec<_>;

    if cmds.iter().any(|(_, cmd)| {
      matches!(
        cmd,
        Cmd::StmtAll
          | Cmd::Thms(_)
          | Cmd::ThmsAll
          | Cmd::Extra(Extra::Definitions | Extra::TheoremsAll)
          | Cmd::ExtraAll
          | Cmd::Recent { .. }
      )
    }) {
      renderer.prep_mathbox_lookup();
      renderer
        .build_statements(cmds.iter().any(|(_, cmd)| matches!(cmd, Cmd::Thms(_) | Cmd::ThmsAll)));
      let max_recent =
        cmds.iter().fold(0, |m, cmd| if let Cmd::Recent { n, .. } = cmd.1 { m.max(n) } else { m });
      if max_recent > 0 {
        renderer.build_recent(max_recent);
        recent_buffers =
          recents.iter().map(|file| std::fs::read_to_string(file).unwrap()).collect();
        renderer.build_recent_templates(recent_buffers.iter().map(|file| &**file))
      }
    }

    if cmds.iter().any(|(_, cmd)| matches!(cmd, Cmd::StmtAll)) {
      renderer.build_used_by();
    }

    for (alt, cmd) in cmds {
      match cmd {
        Cmd::StmtAll => {
          let total = renderer.statements.len();
          let done = AtomicU32::new(0);
          let last = RwLock::new(Instant::now());
          renderer.statements.par_iter().for_each(|&stmt| {
            let label = as_str(stmt.label());
            let w = &mut BufWriter::new(File::create(format!("{label}.html")).unwrap());
            renderer.show_statement(w, stmt, alt).unwrap();
            let end = Instant::now();
            let done = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            let start2 = *last.read().unwrap();
            if (end - start2).as_millis() > 1000 {
              *last.write().unwrap() = end;
              println!("[{done}/{total}] rendering {}", label);
            }
          })
        }
        Cmd::Stmt(label) => {
          let stmt = db.statement(label.as_bytes()).unwrap();
          let w = &mut std::io::stdout();
          renderer.show_statement(w, stmt, alt).unwrap()
        }
        Cmd::ThmsAll => {
          let num_pages = renderer.num_pages();
          (0..num_pages).into_par_iter().map(Some).chain(rayon::iter::once(None)).for_each(|page| {
            let file = match page {
              Some(page) => File::create(format!("mmtheorems{}.html", page + 1)),
              None => File::create("mmtheorems.html"),
            };
            renderer
              .show_theorems(&mut BufWriter::new(file.unwrap()), page, num_pages, alt)
              .unwrap();
          })
        }
        Cmd::Thms(page) => {
          let num_pages = renderer.num_pages();
          let w = &mut std::io::stdout();
          let page = page.checked_sub(1);
          if let Some(page) = page {
            assert!(
              page * THMS_PER_PAGE < renderer.statements.len(),
              "theorems page out of range, max = {num_pages}",
            );
          }
          renderer.show_theorems(w, page, num_pages, alt).unwrap()
        }
        Cmd::Extra(extra) => {
          let w = &mut std::io::stdout();
          renderer.show_extra(w, extra, alt).unwrap();
        }
        Cmd::ExtraAll =>
          [Extra::Ascii, Extra::Definitions, Extra::TheoremsAll].into_par_iter().for_each(|extra| {
            let w = &mut BufWriter::new(File::create(format!("{}.html", extra.label())).unwrap());
            renderer.show_extra(w, extra, alt).unwrap();
          }),
        Cmd::Recent { n, in_, out_ } => {
          let w = &mut BufWriter::new(File::create(out_).unwrap());
          renderer.show_recent(w, n, in_, alt).unwrap();
        }
      }
    }
  } else {
    #[cfg(not(feature = "server"))]
    panic!("re-compile with 'server' feature enabled");

    #[cfg(feature = "server")]
    run_server(iter)
  }
}

#[cfg(feature = "server")]
fn run_server(args: impl Iterator<Item = String>) {
  let mut args = args.peekable();
  use actix_web::{
    get, rt::System, web::Data, web::Path, App, HttpResponse, HttpServer, Responder,
  };
  use std::collections::HashMap;
  let mut renderers = HashMap::new();
  while let Some(route) = args.next() {
    let file = args.next().unwrap();
    let mut db = Box::new(new_db(file));
    db.grammar_pass();
    let mut renderer = Renderer::new(&*Box::leak(db));
    renderer.prep_mathbox_lookup();
    renderer.build_statements(true);
    if let Some("--recent") = args.peek().map(|x| &**x) {
      args.next();
      let n = args.next().unwrap().parse().expect("expected integer");
      let file = args.next().unwrap();
      let recent = &*std::fs::read_to_string(file).unwrap().leak();
      renderer.build_recent(n);
      renderer.build_recent_templates(std::iter::once(recent));
    }
    renderers.insert(route, renderer);
  }
  let renderers = Data::new(renderers);
  System::new("server")
    .block_on(async move {
      println!("starting server, open http://localhost:8080/");
      HttpServer::new(move || {
        App::new().app_data(renderers.clone()).service(render_thm_uni).service(render_thm_gif)
      })
      .bind("localhost:8080")?
      .run()
      .await
    })
    .unwrap();

  fn theorems_page(r: &Renderer<'_>, page: &str) -> Option<Option<usize>> {
    let page = page.strip_prefix("mmtheorems")?;
    if page.is_empty() {
      return Some(None)
    }
    let page = page.parse::<usize>().ok()?.checked_sub(1)?;
    if page.checked_mul(THMS_PER_PAGE)? >= r.statements.len() {
      return None
    }
    Some(Some(page))
  }

  fn recent_page(r: &Renderer<'_>, page: &str) -> Option<(usize, usize)> {
    let page = page.strip_prefix("mmrecent")?;
    let page = if page.is_empty() { 100 } else { page.parse::<usize>().ok()? };
    if 0 < page && page <= r.recent.len() {
      return Some((0, page))
    }
    None
  }

  fn render_thm(
    rs: &HashMap<String, Renderer<'static>>, db: String, label: String, alt: bool,
  ) -> impl Responder {
    let Some(r) = rs.get(&db) else { return HttpResponse::NotFound().into() };
    let mut w = vec![];
    let now = std::time::Instant::now();
    if label.starts_with("mm") {
      if let Some(page) = theorems_page(r, &label) {
        r.show_theorems(&mut w, page, r.num_pages(), alt).unwrap();
      } else if let Ok(extra) = label.parse() {
        r.show_extra(&mut w, extra, alt).unwrap();
      } else if let Some((tpl, n)) = recent_page(r, &label) {
        r.show_recent(&mut w, n, tpl, alt).unwrap();
      } else {
        return HttpResponse::NotFound().into()
      }
    } else {
      let Some(stmt) = r.db.statement(label.as_bytes()) else {
        return HttpResponse::NotFound().into()
      };
      if !stmt.is_assertion() {
        return HttpResponse::NotFound().into()
      };
      r.show_statement(&mut w, stmt, alt).unwrap();
    }
    println!("rendered {} in {}ms", label, now.elapsed().as_millis());
    HttpResponse::Ok().body(w)
  }

  #[get("/{db}uni/{label}.html")]
  async fn render_thm_uni(
    data: Data<HashMap<String, Renderer<'static>>>, Path((db, label)): Path<(String, String)>,
  ) -> impl Responder {
    render_thm(&data, db, label, true)
  }

  #[get("/{db}gif/{label}.html")]
  async fn render_thm_gif(
    data: Data<HashMap<String, Renderer<'static>>>, Path((db, label)): Path<(String, String)>,
  ) -> impl Responder {
    render_thm(&data, db, label, false)
  }
}
