thunk : forall a. (Unit -> a) -> a
      = \server: f . f ();

// - List library

data List a = Nil | Cons a (List a) ;

mapWithCount : forall a b. Int -> (a -> Int -> b) -> List a -> List b
    = \idx f xs.
        case xs {
         Nil => Nil;
         Cons y ys => Cons (f y idx) (mapWithCount (idx + 1) f ys)
        };

mapOnIndex : forall a. Int -> (a -> a) -> List a -> List a
    = \targetIdx f xs.
        mapWithCount 0 (\av idx.
          if (targetIdx - idx) >= 0 then if (targetIdx - idx) <= 0 then f av else av else av) xs;

count : forall a. List a -> Int
    = \xs .
        case xs {
          Nil => 0;
          Cons y ys => 1 + (count ys)
      };

filter : forall a. (a -> Bool) -> List a -> List a
    = \pred xs.
        case xs {
           Nil => Nil;
           Cons y ys =>
             if (pred y) then Cons y (filter pred ys)
             else (filter pred ys)
      };

delete : forall a. Int -> List a -> List a
       = \idx xs.
           case xs {
             Nil => Nil;
             Cons y ys =>
               if idx < 1 then ys
               else Cons y (delete (idx - 1) ys)
           };

map : forall a b. (a -> b) -> List a -> List b
    = \f xs.
        mapWithCount 0 (\av idx. f av) xs;

// - HTML

// nl : forall a. List a
//    = Nil;

cs : forall a. a -> List a -> List a
   = \client: w lst. Cons w lst;

data Html a = Element String (List (Attr a)) (List (Html a)) | Txt String;

data Attr a = Property String String | Attribute String String | EventBind String a | KeyBind Int a 
            | ValueBind String (String -client-> a);

onClick : forall a. a -> Attr a
        = \client: msg. EventBind "click" msg;
onDblClick : forall a. a -> Attr a
        = \client: msg. EventBind "dblclick" msg;
onBlur : forall a. a -> Attr a
        = \client: msg. EventBind "blur" msg;
onEnter : forall a. a -> Attr a
        = \client: msg. KeyBind 13 msg;
onInput : forall a. (String -> a) -> Attr a
        = \client: msgF. ValueBind "input" msgF;

nlH : List (Html Msg)
    = Nil;

nlA : List (Attr Msg)
    = Nil;

csH : Html Msg -> List (Html Msg) -> List (Html Msg)  // Todo: Is this mandatory or optional to give a hint, i.e., {client}?
    = \client: h t. cs h t;  // Todo: csH is a client function since so is cs.

csA : Attr Msg -> List (Attr Msg) -> List (Attr Msg)
    = \client: h t. cs h t;

// // Page is: init x view x update x mount point (query selector e.g., #id)
data Page a e = Page a ( client: a -> Html e) ( client: e -> a -> a ) String; 
        // Todo: client: a -> Html e and client: e -> a -> a 
        //   vs. client: Page a (a -> Html e) (e -> a -> a) 
        //   vs. Page {client} a e ???

data TodoItem = TodoItem String Bool Bool;

data Model = Content String (List TodoItem) (Ref {server} (List TodoItem)); 

data Selected = All | Active | Completed;

data Msg = Update String | Submit
         | Toggle Int | Delete Int | Editing Int | Change Int String | Commit Int
         | ClearCompleted | ToggleAll
         | Select Selected;

toggleEditing: TodoItem -> TodoItem
          = \ti.
              case ti { TodoItem content done editing =>
                TodoItem content done (if editing then False else True)
              };
toggleItem: TodoItem -> TodoItem
          = \ti.
              case ti { TodoItem content done editing =>
                TodoItem content (if done then False else True) editing
              };

newContent: String -> TodoItem -> TodoItem
          = \str ti.
              case ti { TodoItem content done editing => TodoItem str done editing };

showItem: TodoItem -> Int -> Html Msg
        = \client: item idx.
            case item { TodoItem content done editing =>
              Element "li" (csA (Attribute "class"
                (concat (if done then "completed" else "") (if editing then "editing" else ""))
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

showList: List TodoItem -> Html Msg
        = \client: items.
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
                (mapWithCount 0 showItem items))
            nlH)));

header : String -> Html Msg
       = \client: str.
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


footer : Int -> Html Msg
       = \client: count.
           Element "footer" (csA (Attribute "class" "footer") nlA)
             (csH (Element "span" (csA (Attribute "class" "todo-count") nlA)
               (csH (Txt (concat (intToString count) " items left")) nlH))
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

view : Model -> Html Msg
     = \client: m.
          case m { Content str visibleList ref =>
            // let { tds: List [TodoItem] = (! ref) } // Todo: ! ref vs ! {server} ref
              Element "div" nlA
	      // (csH (Element "link"
	        // (csA (Attribute "rel" "stylesheet")
	        // (csA (Attribute "href" "r/index.css")
		// nlA)) nlH)
              (csH (header str)
              (csH (showList visibleList)
              (csH (footer (count 
                (filter 
                  (\client: ti. case ti { TodoItem txt done e => if done then False else True }) // Todo: If ommitted, {client}??
                  visibleList)))
	      // (csH (Element "link"
	      //  (csA (Attribute "rel" "stylesheet")
	      //  (csA (Attribute "href" "r/base.css")
	      //	nlA)) nlH)
              nlH))) // ))

            // end
          };

isNotDone : TodoItem -> Bool
     = \client: ti. case ti { TodoItem txt done e => if done then False else True };
isDone : TodoItem -> Bool
     = \client: ti. case ti { TodoItem txt done e => done };

update : Msg -> Model -> Model
       = \client: msg model.
          case model { Content line visibleList ref =>
            case msg {
              Update str => Content str visibleList ref;
              Submit =>
                case (((\server: x.
                  ref :=  (Cons (TodoItem line False False)  // Todo: := server vs. :=
                    (! ref))
                ) ()), model) { (u, m) => Content "" (! ref) ref };
              Toggle idx =>
                // FIXME Look at let errors? typer
                case (((\server: x.
                  ref := (mapOnIndex idx toggleItem
                    (! ref))
//               let { todos: List TodoItem = ! ref;
//                     res: List TodoItem = mapOnIndex idx toggleItem todos
//                   }
//                 ref := res
//               end
                ) ()), model) { (u, m) => Content line (! ref) ref };

              Delete idx =>
                case (((\server: x.
                  ref := (delete idx (! ref))
                ) ()), model) { (u, m) => Content line (! ref) ref };

              ClearCompleted =>
                case (((\server: x.   // Todo: fine-tune location of computation
                  ref :=  
                    (filter isNotDone (! ref))
                ) ()), model) { (u, m) => Content line (! ref) ref };

              ToggleAll =>
                case (((\server: x.
                  ref :=
                    (map toggleItem (! ref))
                ) ()), model) { (u, m) => Content line (! ref) ref };

              Select selected =>
                case selected {
                  All => Content line (! ref) ref;
                  Active => Content line (filter isNotDone (! ref)) ref;  // Todo: filter @ client, but ! ref @ server
                  Completed => Content line (filter isDone (! ref)) ref
                };

              Editing idx =>
                case (((\server: x.
                  ref := 
                    (mapOnIndex idx toggleEditing visibleList)
                ) ()), model) { (u, m) => Content line (! ref) ref };

              Commit idx =>
                case (((\server: x.
                  ref :=
                    (mapOnIndex idx toggleEditing visibleList)
                ) ()), model) { (u, m) => Content line (! ref) ref };

              Change idx str =>
                case (((\server: x.
                  ref :=
                    (mapOnIndex idx (newContent str) visibleList)
                ) ()), model) { (u, m) => Content line (! ref) ref }
          }};

serverModel : Ref {server} (List TodoItem)   // Todo: Ref (List TodoItem) vs. Ref {server} (List TodoItem) !!!
            = thunk (\server: u. ref Nil);  //       Could write ``ref Nil @ server" ??

init : Model
     = Content "" (! serverModel) serverModel;

main : Page Model Msg
     = Page init view update "body"

