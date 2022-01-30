mod render;

use actix_web::{get, web, App, HttpResponse, HttpServer, Responder};
use lazy_static::lazy_static;
use metamath_knife::Database;
use render::Renderer;

lazy_static! {
  static ref DB: Box<Database> = {
    let mut db = Box::new(Database::default());
    db.parse("../mm/set.mm".into(), vec![]);
    db.scope_pass();
    db.typesetting_pass();
    db
  };
  static ref RENDERER: Renderer<'static> = Renderer::new(&DB);
}
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
    renderer.show_statement(w, stmt, true, true).unwrap();
  } else {
    actix_web::rt::System::new("server")
      .block_on(async move {
        println!("starting server, open http://localhost:8080/");
        HttpServer::new(|| App::new().service(render_thm)).bind("localhost:8080")?.run().await
      })
      .unwrap()
  }
}

#[get("/mpeuni/{label}.html")]
async fn render_thm(web::Path(label): web::Path<String>) -> impl Responder {
  let stmt = DB.statement(label.as_bytes()).unwrap();
  let mut w = vec![];
  RENDERER.show_statement(&mut w, stmt, true, true).unwrap();
  HttpResponse::Ok().body(w)
}
