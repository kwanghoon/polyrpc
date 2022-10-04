thunk : [a]. (Unit -server-> a) -server-> a
      = [a]. \f: Unit -server-> a @ server. f ();

data List = [a]. Nil | Cons a (List [a]) ;

mapWithCount : {l1 l2}. [a b]. (Int -l2-> (a -l1-> Int -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}. [a b].
      \idx: Int @ l2 f: a -l1-> Int -l1-> b @ l2 xs:List [a] @ l2 .
        case xs {
         Nil => Nil [b];
         Cons y ys => Cons [b] (f y idx) (mapWithCount {l1 l2} [a b] (idx + 1) f ys)
        };

mapOnIndex : {l1 l2}. [a]. (Int -l2-> (a -l1-> a) -l2-> List [a] -l2-> List [a])
    = {l1 l2}. [a].
      \targetIdx: Int @ l2 f:a -l1->a @ l2 xs:List [a] @l2 .
        mapWithCount {l1 l2} [a a] 0 (\av: a @ l1 idx: Int @ l1.
          if (targetIdx - idx) >= 0 then if (targetIdx - idx) <= 0 then f av else av else av) xs;

count : {l1}. [a]. (List [a] -l1-> Int)
    = {l1}. [a].
      \xs: List [a] @ l1.
        case xs {
          Nil => 0;
          Cons y ys => 1 + (count {l1} [a] ys)
      };

filter : {l1}. [a]. ((a -l1-> Bool) -l1-> List [a] -l1-> List [a])
    = {l1}. [a].
      \pred: a -l1-> Bool @ l1 xs: List [a] @ l1.
        case xs {
           Nil => Nil [a];
           Cons y ys =>
             if (pred y) then Cons [a] y (filter {l1} [a] pred ys)
             else (filter {l1} [a] pred ys)
      };

delete : {l}. [a]. (Int -l-> List [a] -l-> List [a])
       = {l}. [a].
         \idx: Int @ l xs : List [a] @ l.
           case xs {
             Nil => Nil [a];
             Cons y ys =>
               if idx < 1 then ys
               else Cons [a] y (delete {l} [a] (idx - 1) ys)
           };

map : {l1 l2}. [a b]. ((a -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}. [a b].
      \f:a -l1->b @l2 xs:List [a] @l2 .
        mapWithCount {l1 l2} [a b] 0 (\av: a @ l1 idx: Int @ l1. f av) xs;

nl : [a]. List [a]
   = [a]. Nil [a];

cs : [a]. a -client-> List [a] -client-> List [a]
   = [a]. \w: a @ client
           lst: List [a] @ client. Cons [a] w lst;

data Html = [a]. Element String (List [Attr [a]]) (List [Html [a]]) | Txt String;
data Attr = [a]. Property String String | Attribute String String | EventBind String a | KeyBind Int a | ValueBind String (String -client-> a);

onClick : [a]. a -client-> Attr [a]
        = [a]. \msg: a @ client. EventBind [a] "click" msg;
onDblClick : [a]. a -client-> Attr [a]
        = [a]. \msg: a @ client. EventBind [a] "dblclick" msg;
onBlur : [a]. a -client-> Attr [a]
        = [a]. \msg: a @ client. EventBind [a] "blur" msg;
onEnter : [a]. a -client-> Attr [a]
        = [a]. \msg: a @ client. KeyBind [a] 13 msg;
onInput : [a]. (String -client-> a) -client-> Attr [a]
        = [a]. \msgF: (String -client-> a) @ client. ValueBind [a] "input" msgF;

nlH : List [Html [Msg]]
    = Nil [Html [Msg]];

nlA : List [Attr [Msg]]
    = Nil [Attr [Msg]];

csH : Html [Msg] -client-> List [Html [Msg]] -client-> List [Html [Msg]]
    = cs [Html [Msg]];

csA : Attr [Msg] -client-> List [Attr [Msg]] -client-> List [Attr [Msg]]
    = cs [Attr [Msg]];

// Page is: init x view x update x mount point (query selector e.g., #id)
data Page = [a e]. Page a (a -client-> Html [e]) (e -client-> a -client-> a) String;

data TodoItem = TodoItem String Bool Bool;
data Model = Content String (List [TodoItem]) (Ref {server} [List [TodoItem]]);
data Selected = All | Active | Completed;
data Msg = Update String | Submit
         | Toggle Int | Delete Int | Editing Int | Change Int String | Commit Int
         | ClearCompleted | ToggleAll
         | Select Selected;

toggleEditing: {l}. TodoItem -l-> TodoItem
          = {l}. \ti : TodoItem @ l.
              case ti { TodoItem content done editing =>
                TodoItem content done (if editing then False else True)
              };
toggleItem: {l}. TodoItem -l-> TodoItem
          = {l}. \ti : TodoItem @ l.
              case ti { TodoItem content done editing =>
                TodoItem content (if done then False else True) editing
              };

newContent: {l}. String -l-> TodoItem -l-> TodoItem
          = {l}. \str: String @ l ti : TodoItem @ l.
              case ti { TodoItem content done editing => TodoItem str done editing };

showItem: TodoItem -client-> Int -client-> Html [Msg]
        = \item: TodoItem @ client idx: Int @ client.
            case item { TodoItem content done editing =>
              Element [Msg] "li" (csA (Attribute [Msg] "class"
                (concat {client} (if done then "completed" else "") (if editing then "editing" else ""))
                ) nlA)
              (csH (Element [Msg] "div" (csA (Attribute [Msg] "class" "view") nlA)
                (csH (Element [Msg] "input" (csA (Attribute [Msg] "class" "toggle")
                                            (csA (Attribute [Msg] "type" "checkbox")
                                            (csA (onClick [Msg] (Toggle idx))
                                            (csA (Property [Msg] "checked" (if done then "false" else "true")) nlA))))
                                            nlH)
                (csH (Element [Msg] "label"
                  (csA (onDblClick [Msg] (Editing idx)) nlA)
                  (csH (Txt [Msg] content) nlH))
                (csH (Element [Msg] "button" (csA (Attribute [Msg] "class" "destroy")
                                             (csA (onClick [Msg] (Delete idx))
                                             nlA)) nlH)
                nlH)))
              )
              (csH (Element [Msg] "input"
                (csA (Attribute [Msg] "class" "edit")
                (csA (Property [Msg] "value" content)
                (csA (onInput [Msg] (Change idx))
                (csA (onEnter [Msg] (Commit idx))
                (csA (onBlur [Msg] (Commit idx))
                nlA)))))
                nlH)
              nlH))
            };

showList: List [TodoItem] -client-> Html [Msg]
        = \items: List [TodoItem] @ client.
          Element [Msg] "section"
            (csA (Attribute [Msg] "class" "main")
            (csA (Attribute [Msg] "style" "display; block")
            nlA))
            (csH (Element [Msg] "input"
              (csA (Attribute [Msg] "id" "toggle-all")
              (csA (Attribute [Msg] "class" "toggle-all")
              (csA (Attribute [Msg] "type" "checkbox")
              (csA (onClick [Msg] ToggleAll)
              nlA)))) nlH)
            (csH (Element [Msg] "label" (csA (Attribute [Msg] "for" "toggle-all") nlA) nlH)
            (csH (Element [Msg] "ul" (csA (Attribute [Msg] "class" "todo-list") nlA)
                (mapWithCount {client client} [TodoItem (Html [Msg])] 0 showItem items))
            nlH)));


header : String -client-> Html [Msg]
       = \str: String @ client.
           Element [Msg] "header" (csA (Attribute [Msg] "class" "header") nlA)
             (csH (Element [Msg] "h1" nlA (csH (Txt [Msg] "todos") nlH))
             (csH (Element [Msg] "input"
               (csA (Attribute [Msg] "class" "new-todo")
               (csA (Attribute [Msg] "placeholder" "What needs to be done?")
               (csA (Property [Msg] "value" str)
               (csA (onInput [Msg] Update)
               (csA (onEnter [Msg] Submit)
               nlA)))))
               (csH (Txt [Msg] "todos") nlH))
             nlH));


footer : Int -client-> Html [Msg]
       = \count: Int @ client.
           Element [Msg] "footer" (csA (Attribute [Msg] "class" "footer") nlA)
             (csH (Element [Msg] "span" (csA (Attribute [Msg] "class" "todo-count") nlA)
               (csH (Txt [Msg] (concat {client} (intToString {client} count) " items left")) nlH))
             (csH (Element [Msg] "ul" (csA (Attribute [Msg] "class" "filters") nlA)
               (csH (Element [Msg] "li" nlA (csH (Element [Msg] "a"
                 (csA (onClick [Msg] (Select All)) nlA)
                 ((csH (Txt [Msg] "All") nlH))) nlH))
               (csH (Element [Msg] "li" nlA (csH (Element [Msg] "a"
                 (csA (onClick [Msg] (Select Active)) nlA)
                 ((csH (Txt [Msg] "Active") nlH))) nlH))
               (csH (Element [Msg] "li" nlA (csH (Element [Msg] "a"
                 (csA (onClick [Msg] (Select Completed)) nlA)
                 ((csH (Txt [Msg] "Completed") nlH))) nlH))
               nlH))))
             (csH (Element [Msg] "button"
               (csA (Attribute [Msg] "class" "clear-completed")
               (csA (onClick [Msg] (ClearCompleted))
               nlA))
               (csH (Txt [Msg] "Clear completed") nlH))
             nlH)));

view : Model -client-> Html [Msg]
     = \m: Model @ client.
          case m { Content str visibleList ref =>
            // let { tds: List [TodoItem] = (! {server} [List [TodoItem]] ref) }
              Element [Msg] "div" nlA
              (csH (header str)
              (csH (showList visibleList)
              (csH (footer (count {client} [TodoItem]
                (filter {client} [TodoItem]
                  (\ti: TodoItem @ client. case ti { TodoItem txt done e => if done then False else True })
                  visibleList)))
              nlH)))

            // end
          };

isNotDone : TodoItem -client-> Bool
     = \ti : TodoItem @ client. case ti { TodoItem txt done e => if done then False else True };
isDone : TodoItem -client-> Bool
     = \ti : TodoItem @ client. case ti { TodoItem txt done e => done };

update : Msg -client-> Model -client-> Model
       = \msg: Msg @ client model: Model @ client.
          case model { Content line visibleList ref =>
            case msg {
              Update str => Content str visibleList ref;
              Submit =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]] (Cons [TodoItem] (TodoItem line False False)
                    (! {server} [List [TodoItem]] ref))
                ) ()), model) { (u, m) => Content "" (! {server} [List [TodoItem]] ref) ref };
              Toggle idx =>
                // FIXME Look at let errors? typer
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]] (mapOnIndex {server server} [TodoItem] idx (toggleItem {server})
                    (! {server} [List [TodoItem]] ref))
//               let { todos: List [TodoItem] = ! {server} [List [TodoItem]] ref;
//                     res: List [TodoItem] = mapOnIndex {server server} [TodoItem] idx (toggleItem {server}) todos
//                   }
//                 ref := {server} [List [TodoItem]] res
//               end
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              Delete idx =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]] (delete {server} [TodoItem] idx (! {server} [List [TodoItem]] ref))
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              ClearCompleted =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]]
                    (filter {client} [TodoItem] isNotDone (! {server} [List [TodoItem]] ref))
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              ToggleAll =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]]
                    (map {server server} [TodoItem TodoItem] (toggleItem {server}) (! {server} [List [TodoItem]] ref))
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              Select selected =>
                case selected {
                  All => Content line (! {server} [List [TodoItem]] ref) ref;
                  Active => Content line (filter {client} [TodoItem] isNotDone (! {server} [List [TodoItem]] ref)) ref;
                  Completed => Content line (filter {client} [TodoItem] isDone (! {server} [List [TodoItem]] ref)) ref
                };

              Editing idx =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]]
                    (mapOnIndex {server server} [TodoItem] idx (toggleEditing {server}) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              Commit idx =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]]
                    (mapOnIndex {server server} [TodoItem] idx (toggleEditing {server}) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref };

              Change idx str =>
                case (((\x: Unit @ server.
                  ref := {server} [List [TodoItem]]
                    (mapOnIndex {server server} [TodoItem] idx (newContent {server} str) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} [List [TodoItem]] ref) ref }
          }};


serverModel : Ref {server} [List [TodoItem]]
            = thunk [Ref {server} [List [TodoItem]]] (\u: Unit @ server. ref {server} [List [TodoItem]] (Nil [TodoItem]));

init : Model
     = Content "" (! {server} [List [TodoItem]] serverModel) serverModel;

main : Page [Model Msg]
     = Page [Model Msg] init view update "#body"
