mod render;

use metamath_knife::{as_str, Database};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use render::Renderer;
use std::{fs::File, time::Instant};

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
  let mut db = Database::default();
  db.parse(file, vec![]);
  db.scope_pass();
  db.typesetting_pass();
  let mut renderer = Renderer::new(&db);

  if let Some((alt, label)) = label {
    if label == "*" {
      renderer.prep_mathbox_lookup();
      // FIXME: this seems wasteful, should the db expose a par_iter interface?
      db.statements().collect::<Vec<_>>().par_iter().for_each(|&stmt| {
        let start = Instant::now();
        let label = as_str(stmt.label());
        renderer
          .show_statement(&mut File::create(format!("{label}.html")).unwrap(), stmt, alt)
          .unwrap();
        println!("rendered {} in {}ms", label, start.elapsed().as_millis());
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
      renderer.prep_mathbox_lookup();
      actix_web::rt::System::new("server")
        .block_on(async move {
          println!("starting server, open http://localhost:8080/");
          actix_web::HttpServer::new(|| {
            actix_web::App::new().service(render_thm_mpeuni).service(render_thm_mpegif)
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
fn render_thm(label: String, alt: bool) -> impl actix_web::Responder {
  lazy_static::lazy_static! {
    static ref DB: Box<Database> = {
      let mut db = Box::<Database>::default();
      db.parse("../mm/set.mm".into(), vec![]);
      db.scope_pass();
      db.typesetting_pass();
      db
    };
    static ref RENDERER: Renderer<'static> = Renderer::new(&DB);
  }

  let stmt = DB.statement(label.as_bytes()).unwrap();
  let mut w = vec![];
  let now = std::time::Instant::now();
  RENDERER.show_statement(&mut w, stmt, alt).unwrap();
  println!("rendered {} in {}ms", label, now.elapsed().as_millis());
  actix_web::HttpResponse::Ok().body(w)
}

#[cfg(feature = "server")]
#[actix_web::get("/mpeuni/{label}.html")]
async fn render_thm_mpeuni(
  actix_web::web::Path(label): actix_web::web::Path<String>,
) -> impl actix_web::Responder {
  render_thm(label, true)
}

#[cfg(feature = "server")]
#[actix_web::get("/mpegif/{label}.html")]
async fn render_thm_mpegif(
  actix_web::web::Path(label): actix_web::web::Path<String>,
) -> impl actix_web::Responder {
  render_thm(label, false)
}
