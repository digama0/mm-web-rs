mod render;

use metamath_knife::Database;
use render::Renderer;

fn main() {
  let mut iter = std::env::args().skip(1);
  let label = match iter.next().as_deref() {
    Some("write") => Some(iter.next().unwrap()),
    Some("server") => None,
    _ => panic!("use 'mm-web-rs write LABEL' or 'mm-web-rs server'"),
  };
  let mut db = Database::default();
  db.parse("../mm/set.mm".into(), vec![]);
  db.scope_pass();
  db.typesetting_pass();
  let renderer = Renderer::new(&db);

  if let Some(label) = label {
    let stmt = db.statement(label.as_bytes()).unwrap();
    // let mut w = &mut File::create(format!("{}.html", label)).unwrap();
    let w = &mut std::io::stdout();
    renderer.show_statement(w, stmt, true, false).unwrap();
  } else {
    #[cfg(not(feature = "server"))]
    panic!("re-compile with 'server' feature enabled");

    #[cfg(feature = "server")]
    actix_web::rt::System::new("server")
      .block_on(async move {
        println!("starting server, open http://localhost:8080/");
        actix_web::HttpServer::new(|| actix_web::App::new().service(render_thm2))
          .bind("localhost:8080")?
          .run()
          .await
      })
      .unwrap()
  }
}

#[cfg(feature = "server")]
fn render_thm(label: String) -> impl actix_web::Responder {
  lazy_static::lazy_static! {
    static ref DB: Box<Database> = {
      let mut db = Box::new(Database::default());
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
  RENDERER.show_statement(&mut w, stmt, true, false).unwrap();
  println!("rendered {} in {}ms", label, now.elapsed().as_millis());
  actix_web::HttpResponse::Ok().body(w)
}

#[cfg(feature = "server")]
#[actix_web::get("/mpeuni/{label}.html")]
async fn render_thm2(
  actix_web::web::Path(label): actix_web::web::Path<String>,
) -> impl actix_web::Responder {
  render_thm(label)
}
