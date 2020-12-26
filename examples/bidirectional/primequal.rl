b1 : Bool = "abc" == "abc";
b2 : Bool = 12345 == 12345;
b3 : Bool = True  == True;

b4 : Bool = "def" == "ghi";
b5 : Bool = 67890 == 16273;
b6 : Bool = False == True;

test1 : Unit =
  if b1 and b2 and b3
  then print {client} "b1 and b2 and b3: True\n"
  else print {client} "b1 and b2 and b3: False\n";

test2 : Unit =
  if b4 or b5 or b6
  then print {client} "b4 or b5 or b6: True\n"
  else print {client} "b4 or b5 or b6: False\n"



