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

cs : [a]. a -client-> List [a] -client-> List [a]
   = \w @ client
      lst @ client. Cons w lst;

data Html = [a]. Element String (List [Attr [a]]) (List [Html [a]]) | Txt String;
data Attr = [a]. Property String String | Attribute String String | EventBind String a | KeyBind Int a | ValueBind String (String -client-> a);

onClick : [a]. a -client-> Attr [a]
        = \msg @ client. EventBind "click" msg;
	
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

toggleItem: {l}. TodoItem -l-> TodoItem
          = {l}. \ti @ l.
              case ti { TodoItem content done editing =>
                TodoItem content (if done then False else True) editing
              };

showItem: TodoItem -client-> Int -client-> Html [Msg]
        = \item @ client idx @ client.
            case item { TodoItem content done editing =>
              Element "li" nlA
               (csH (Element "input" (csA (Attribute "type" "checkbox")
                                            (csA (onClick (Toggle idx))
                                            (csA (Property "checked" (if done then "false" else "true")) nlA)))
                                            nlH)
               (csH (Element "label" nlA (csH (Txt content) nlH))
               (csH (Element "button" (csA (onClick (Delete idx)) nlA)
	              (csH (Txt "[X]") nlH))
                nlH)))
            };

showList : List [TodoItem] -client-> Html [Msg]
        = \items @ client.
          Element  "ul" nlA
                (mapWithCount {client client} 0 showItem items);

header : String -client-> Html [Msg]
       = \str @ client.
             Element "input"
               (csA (Attribute "placeholder" "What needs to be done?")
               (csA (Property "value" str)
               (csA (onInput Update)
               (csA (onEnter Submit)
               nlA))))
               nlH;


view : Model -client-> Html [Msg]
     = \m @ client.
          case m { Content str visibleList ref =>
              Element "div" nlA
                (csH (header str)
                (csH (showList visibleList)
                nlH))
          };

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
                case (((\x @ server.
                  ref := {server} (mapOnIndex {server server} idx (toggleItem {server})
                    (! {server} ref))
                ) ()), model) { (u, m) => Content line (! {server} ref) ref };

              Delete idx =>
                case (((\x @ server.
                  ref := {server} (delete {server} idx (! {server} ref))
                ) ()), model) { (u, m) => Content line (! {server} ref) ref }

          }};

serverModel : Ref {server} [List [TodoItem]]
            = thunk (\u @ server. ref {server} Nil);

init : Model
     = Content "" (! {server} serverModel) serverModel;

main : Page [Model Msg]
     = Page init view update "body"
