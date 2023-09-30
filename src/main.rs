mod render;

use metamath_knife::{as_str, database::DbOptions, Database, StatementType};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use render::Renderer;
use std::{
  fs::File,
  io::BufWriter,
  sync::{atomic::AtomicU32, RwLock},
  time::Instant,
};

fn main() {
  let mut iter = std::env::args().skip(1);
  let file = iter.next().unwrap();
  let label = match iter.next().as_deref() {
    Some("write") => {
      let alt = match &*iter.next().unwrap() {
        "gif" => false,
        "uni" => true,
        _ => panic!("expected 'gif' or 'uni'"),
      };
      Some((alt, iter.next().unwrap()))
    }
    Some("server") => None,
    _ => panic!("use 'mm-web-rs <DB> write <gif|uni> <LABEL|*>' or 'mm-web-rs <DB> server'"),
  };
  let mut db = Database::new(DbOptions { incremental: true, ..DbOptions::default() });
  db.parse(file.clone(), vec![]);
  assert!(
    db.statements().next().unwrap().statement_type() != StatementType::Eof,
    "file {file} empty or not found"
  );
  db.scope_pass();
  db.typesetting_pass();
  if label.as_ref().map_or(true, |(_, label)| {
    label == "*" || db.statement(label.as_bytes()).unwrap().statement_type() == StatementType::Axiom
  }) {
    db.grammar_pass();
  }

  if let Some((alt, label)) = label {
    let mut renderer = Renderer::new(&db);
    if label == "*" {
      renderer.prep_mathbox_lookup();
      renderer.build_used_by();
      // FIXME: this seems wasteful, should the db expose a par_iter interface?
      let statements = db.statements().filter(|s| s.is_assertion()).collect::<Vec<_>>();
      let total = statements.len();

      let done = AtomicU32::new(0);
      let last = RwLock::new(Instant::now());
      statements.par_iter().for_each(|&stmt| {
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
      });
    } else {
      let stmt = db.statement(label.as_bytes()).unwrap();
      let w = &mut std::io::stdout();
      renderer.show_statement(w, stmt, alt).unwrap();
    }
  } else {
    #[cfg(not(feature = "server"))]
    panic!("re-compile with 'server' feature enabled");

    #[cfg(feature = "server")]
    {
      let mut renderer = Renderer::new(&*Box::leak(Box::new(db)));
      renderer.prep_mathbox_lookup();
      let renderer = actix_web::web::Data::new(renderer);
      actix_web::rt::System::new("server")
        .block_on(async move {
          println!("starting server, open http://localhost:8080/");
          actix_web::HttpServer::new(move || {
            actix_web::App::new()
              .app_data(renderer.clone())
              .service(render_thm_mpeuni)
              .service(render_thm_mpegif)
          })
          .bind("localhost:8080")?
          .run()
          .await
        })
        .unwrap()
    }
  }
}

#[cfg(feature = "server")]
fn render_thm(r: &Renderer<'_>, label: String, alt: bool) -> impl actix_web::Responder {
  let Some(stmt) = r.db.statement(label.as_bytes()) else {
    return actix_web::HttpResponse::NotFound().into()
  };
  if !stmt.is_assertion() {
    return actix_web::HttpResponse::NotFound().into()
  };
  let mut w = vec![];
  let now = std::time::Instant::now();
  r.show_statement(&mut w, stmt, alt).unwrap();
  println!("rendered {} in {}ms", label, now.elapsed().as_millis());
  actix_web::HttpResponse::Ok().body(w)
}

#[cfg(feature = "server")]
#[actix_web::get("/mpeuni/{label}.html")]
async fn render_thm_mpeuni(
  data: actix_web::web::Data<Renderer<'static>>,
  actix_web::web::Path(label): actix_web::web::Path<String>,
) -> impl actix_web::Responder {
  render_thm(&data, label, true)
}

#[cfg(feature = "server")]
#[actix_web::get("/mpegif/{label}.html")]
async fn render_thm_mpegif(
  data: actix_web::web::Data<Renderer<'static>>,
  actix_web::web::Path(label): actix_web::web::Path<String>,
) -> impl actix_web::Responder {
  render_thm(&data, label, false)
}
