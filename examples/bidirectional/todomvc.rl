thunk : [a]. ((Unit -server-> a) -server-> a)
      = \f @ server. f ();

// - List library

data List = [a]. Nil | Cons a (List [a]) ;

mapWithCount : {l1 l2}. [a b]. (Int -l2-> (a -l1-> Int -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}. 
      \idx @ l2 f @ l2 xs @ l2 .
        case xs {
         Nil => Nil;
         Cons y ys => Cons (f y idx) (mapWithCount {l1 l2} (idx + 1) f ys)
        };

mapOnIndex : {l1 l2}. [a]. (Int -l2-> (a -l1-> a) -l2-> List [a] -l2-> List [a])
    = {l1 l2}. 
      \targetIdx @ l2 f @ l2 xs @l2 .
        mapWithCount {l1 l2} 0 (\av @ l1 idx @ l1.
          if (targetIdx - idx) >= 0 then if (targetIdx - idx) <= 0 then f av else av else av) xs;

count : {l1}. [a]. (List [a] -l1-> Int)
    = {l1}. 
      \xs @ l1.
        case xs {
          Nil => 0;
          Cons y ys => 1 + (count {l1} ys)
      };

filter : {l1}. [a]. ((a -l1-> Bool) -l1-> List [a] -l1-> List [a])
    = {l1}. 
      \pred @ l1 xs @ l1.
        case xs {
           Nil => Nil;
           Cons y ys =>
             if (pred y) then Cons y (filter {l1} pred ys)
             else (filter {l1} pred ys)
      };

delete : {l}. [a]. (Int -l-> List [a] -l-> List [a])
       = {l}. 
         \idx @ l xs @ l.
           case xs {
             Nil => Nil;
             Cons y ys =>
               if idx < 1 then ys
               else Cons y (delete {l} (idx - 1) ys)
           };

map : {l1 l2}. [a b]. ((a -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}. 
      \f @l2 xs @l2 .
        mapWithCount {l1 l2} 0 (\av @ l1 idx @ l1. f av) xs;

// - HTML

// nl : [a]. List [a]
//    = Nil;

cs : [a]. a -client-> List [a] -client-> List [a]
   = \w @ client
      lst @ client. Cons w lst;

data Html = [a]. Element String (List [Attr [a]]) (List [Html [a]]) | Txt String;
data Attr = [a]. Property String String | Attribute String String | EventBind String a | KeyBind Int a | ValueBind String (String -client-> a);

onClick : [a]. a -client-> Attr [a]
        = \msg @ client. EventBind "click" msg;
onDblClick : [a]. a -client-> Attr [a]
        = \msg @ client. EventBind "dblclick" msg;
onBlur : [a]. a -client-> Attr [a]
        = \msg @ client. EventBind "blur" msg;
onEnter : [a]. a -client-> Attr [a]
        = \msg @ client. KeyBind 13 msg;
onInput : [a]. (String -client-> a) -client-> Attr [a]
        = \msgF @ client. ValueBind "input" msgF;

nlH : List [Html [Msg]]
    = Nil;

nlA : List [Attr [Msg]]
    = Nil;

csH : Html [Msg] -client-> List [Html [Msg]] -client-> List [Html [Msg]]
    = cs;

csA : Attr [Msg] -client-> List [Attr [Msg]] -client-> List [Attr [Msg]]
    = cs;

// // Page is: init x view x update x mount point (query selector e.g., #id)
data Page = [a e]. Page a (a -client-> Html [e]) (e -client-> a -client-> a) String;

data TodoItem = TodoItem String Bool Bool;
data Model = Content String (List [TodoItem]) (Ref {server} [List [TodoItem]]);
data Selected = All | Active | Completed;
data Msg = Update String | Submit
         | Toggle Int | Delete Int | Editing Int | Change Int String | Commit Int
         | ClearCompleted | ToggleAll
         | Select Selected;

toggleEditing: {l}. TodoItem -l-> TodoItem
          = {l}. \ti @ l.
              case ti { TodoItem content done editing =>
                TodoItem content done (if editing then False else True)
              };
toggleItem: {l}. TodoItem -l-> TodoItem
          = {l}. \ti @ l.
              case ti { TodoItem content done editing =>
                TodoItem content (if done then False else True) editing
              };

newContent: {l}. String -l-> TodoItem -l-> TodoItem
          = {l}. \str @ l ti @ l.
              case ti { TodoItem content done editing => TodoItem str done editing };

showItem: TodoItem -client-> Int -client-> Html [Msg]
        = \item @ client idx @ client.
            case item { TodoItem content done editing =>
              Element "li" (csA (Attribute "class"
                (concat {client} (if done then "completed" else "") (if editing then "editing" else ""))
                ) nlA)
              (csH (Element "div" (csA (Attribute "class" "view") nlA)
                (csH (Element "input" (csA (Attribute "class" "toggle")
                                            (csA (Attribute "type" "checkbox")
                                            (csA (onClick (Toggle idx))
                                            (csA (Property "checked" (if done then "false" else "true")) nlA))))
                                            nlH)
                (csH (Element "label"
                  (csA (onDblClick (Editing idx)) nlA)
                  (csH (Txt content) nlH))
                (csH (Element "button" (csA (Attribute "class" "destroy")
                                             (csA (onClick (Delete idx))
                                             nlA)) nlH)
                nlH)))
              )
              (csH (Element "input"
                (csA (Attribute "class" "edit")
                (csA (Property "value" content)
                (csA (onInput (Change idx))
                (csA (onEnter (Commit idx))
                (csA (onBlur (Commit idx))
                nlA)))))
                nlH)
              nlH))
            };

showList: List [TodoItem] -client-> Html [Msg]
        = \items @ client.
          Element "section"
            (csA (Attribute "class" "main")
            (csA (Attribute "style" "display; block")
            nlA))
            (csH (Element "input"
              (csA (Attribute "id" "toggle-all")
              (csA (Attribute "class" "toggle-all")
              (csA (Attribute "type" "checkbox")
              (csA (onClick ToggleAll)
              nlA)))) nlH)
            (csH (Element "label" (csA (Attribute "for" "toggle-all") nlA) nlH)
            (csH (Element  "ul" (csA (Attribute "class" "todo-list") nlA)
                (mapWithCount {client client} 0 showItem items))
            nlH)));

header : String -client-> Html [Msg]
       = \str @ client.
           Element "header" (csA (Attribute "class" "header") nlA)
             (csH (Element "h1" nlA (csH (Txt "todos") nlH))
             (csH (Element "input"
               (csA (Attribute "class" "new-todo")
               (csA (Attribute "placeholder" "What needs to be done?")
               (csA (Property "value" str)
               (csA (onInput Update)
               (csA (onEnter Submit)
               nlA)))))
               (csH (Txt "todos") nlH))
             nlH));


footer : Int -client-> Html [Msg]
       = \count @ client.
           Element "footer" (csA (Attribute "class" "footer") nlA)
             (csH (Element "span" (csA (Attribute "class" "todo-count") nlA)
               (csH (Txt (concat {client} (intToString {client} count) " items left")) nlH))
             (csH (Element "ul" (csA (Attribute "class" "filters") nlA)
               (csH (Element "li" nlA (csH (Element "a"
                 (csA (onClick (Select All)) nlA)
                 ((csH (Txt "All") nlH))) nlH))
               (csH (Element "li" nlA (csH (Element "a"
                 (csA (onClick (Select Active)) nlA)
                 ((csH (Txt "Active") nlH))) nlH))
               (csH (Element "li" nlA (csH (Element "a"
                 (csA (onClick (Select Completed)) nlA)
                 ((csH (Txt "Completed") nlH))) nlH))
               nlH))))
             (csH (Element "button"
               (csA (Attribute "class" "clear-completed")
               (csA (onClick (ClearCompleted))
               nlA))
               (csH (Txt "Clear completed") nlH))
             nlH)));

view : Model -client-> Html [Msg]
     = \m @ client.
          case m { Content str visibleList ref =>
            // let { tds: List [TodoItem] = (! {server} ref) }
              Element "div" nlA
              (csH (header str)
	      (csH (Element "link"
	        (csA (Attribute "rel" "stylesheet")
	        (csA (Attribute "href" "r/index.css")
		nlA)) nlH)
              (csH (showList visibleList)
              (csH (footer (count {client} 
                (filter {client} 
                  (\ti @ client. case ti { TodoItem txt done e => if done then False else True })
                  visibleList)))
	      (csH (Element "link"
	        (csA (Attribute "rel" "stylesheet")
	        (csA (Attribute "href" "r/base.css")
		nlA)) nlH)
              nlH)))))

            // end
          };

isNotDone : TodoItem -client-> Bool
     = \ti @ client. case ti { TodoItem txt done e => if done then False else True };
isDone : TodoItem -client-> Bool
     = \ti @ client. case ti { TodoItem txt done e => done };

update : Msg -client-> Model -client-> Model
       = \msg @ client model @ client.
          case model { Content line visibleList ref =>
            case msg {
              Update str => Content str visibleList ref;
              Submit =>
                case (((\x @ server.
                  ref := {server}  (Cons (TodoItem line False False)
                    (! {server} ref))
                ) ()), model) { (u, m) => Content "" (! {server} ref) ref };
              Toggle idx =>
                // FIXME Look at let errors? typer
                case (((\x @ server.
                  ref := {server} (mapOnIndex {server server} idx (toggleItem {server})
                    (! {server} ref))
//               let { todos: List [TodoItem] = ! {server} ref;
//                     res: List [TodoItem] = mapOnIndex {server server} idx (toggleItem {server}) todos
//                   }
//                 ref := {server} res
//               end
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              Delete idx =>
                case (((\x @ server.
                  ref := {server} (delete {server} idx (! {server} ref))
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              ClearCompleted =>
                case (((\x @ server.
                  ref := {server} 
                    (filter {client} isNotDone (! {server} ref))
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              ToggleAll =>
                case (((\x @ server.
                  ref := {server} 
                    (map {server server} (toggleItem {server}) (! {server} ref))
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              Select selected =>
                case selected {
                  All => Content line (! {server} ref) ref;
                  Active => Content line (filter {client} isNotDone (! {server} ref)) ref;
                  Completed => Content line (filter {client} isDone (! {server} ref)) ref
                };

              Editing idx =>
                case (((\x @ server.
                  ref := {server} 
                    (mapOnIndex {server server} idx (toggleEditing {server}) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              Commit idx =>
                case (((\x @ server.
                  ref := {server} 
                    (mapOnIndex {server server} idx (toggleEditing {server}) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              Change idx str =>
                case (((\x @ server.
                  ref := {server} 
                    (mapOnIndex {server server} idx (newContent {server} str) visibleList)
                ) ()), model) { (u, m) => Content line (! {server} ref) ref }
          }};

serverModel : Ref {server} [List [TodoItem]]
            = thunk (\u @ server. ref {server} Nil);

init : Model
     = Content "" (! {server} serverModel) serverModel;

main : Page [Model Msg]
     = Page init view update "#body"

