(* version.ml *)
open Unix;;

let release = "2.0";;

let date = 
   let tm = gmtime(time ()) in
   ((string_of_int tm.tm_mday)^"/"^
    (string_of_int (tm.tm_mon+1))^"/"^
    (string_of_int (tm.tm_year+1900)))
;;

let version = (release^" ("^date^")");;

