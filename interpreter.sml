(* 
   The Interpret function assumes a "parse" function, 
      written in another file.
*)

(* ABSTRACT SYNTAX

type Num = int
type Id = string

datatype Exp =
  NumE of Num
| IdE of Id
| AddE of Exp * Exp
| SubE of Exp * Exp
| MulE of Exp * Exp

datatype Comm =
  SkipC
| SeqC of Comm * Comm
| IfC of Exp * Comm * Comm
| WhileC of Exp * Comm
| AssignC of Id * Exp
| OutputC of Exp
| InputC of Id
| ProcCallC of Id * Exp 
| FunCallC of Id * Id * Exp

datatype Decl = 
  ProcD of Id * Id * Comm
| SeqD of Decl * Decl
| NoDecl

datatype Prog = 
  ProgP of Decl * Comm
| ErrorP of string   
*)

(* EXCEPTIONS *)

exception ProcedureNotDeclared of string;
exception EmptyInputStream of Id; 

(* BASIC DEFINITIONS *)

type Val = int  
  (* the values of expressions, and the values that can be stored *)

type ProcVal = Id * Comm 
  (* the formal parameter, and the body, of the procedure *)

(* Global Environment For Functions and Procedures *)

type ProcEnv = (Id * ProcVal) list

(* PEnvInit: unit -> ProcEnv *)
fun PEnvInit () = []

(* PEnvInsert: Id -> ProcVal -> ProcEnv -> ProcEnv *)
fun PEnvInsert id dv penv = (id,dv) :: penv

(* PEnvLookup: ProcEnv -> Id -> ProcVal *)
fun PEnvLookup [] x = raise (ProcedureNotDeclared x)
|   PEnvLookup ((y,dv)::penv) x =
      if x = y then dv 
      else PEnvLookup penv x

(* Stores *)

type GlobalStore = (Id * Val) list  (* for integer identifiers *)

type LocalStore = (Id * Val) list  
   (* for a procedure's parameter, its auxiliary variables (if any),
        and for a special identifier "result"   *)

type Stores = GlobalStore * LocalStore option
   (* the local store only exists inside procedure calls *)

(* StoLookup: (Global/Local)Store -> Id -> Val option   *)
fun StoLookup [] _ = NONE
|   StoLookup ((x1,v1)::s1) x = 
         if x = x1 then SOME v1 else StoLookup s1 x

(* StosLookup: Stores -> Id -> Val option
      first checks the local store   *)
fun StosLookup (global_sto, NONE) x = StoLookup global_sto x
|   StosLookup (global_sto, SOME local_sto) x = 
       StoLookup local_sto x  (* *** MODIFY *)

(* StosUpdate: Id -> Val -> Stores -> Stores *)
fun StosUpdate x v (global_sto, NONE) = ((x,v)::global_sto, NONE)
  (* if local store exists, updates the local store 
       unless variable defined globally but not locally *)
|   StosUpdate x v (global_sto, SOME local_sto) =
       (global_sto,SOME((x,v)::local_sto)) (* *** MODIFY *)

(* EVALUATION OF EXPRESSIONS
     ExpEval: Exp -> Stores -> Val 
*)

fun ExpEval (NumE n) _ = n
|   ExpEval (IdE id) stos = valOf (StosLookup stos id) (* *** MODIFY *)
|   ExpEval (AddE(e1,e2)) stos = ((ExpEval e1 stos) + (ExpEval e2 stos))(*  *** MODIFY *)
|   ExpEval (SubE(e1,e2)) stos = ((ExpEval e1 stos) - (ExpEval e2 stos)) (* *** MODIFY *)
|   ExpEval (MulE(e1,e2)) stos = ((ExpEval e1 stos) * (ExpEval e2 stos)) (* *** MODIFY *)

(* PROCESSING OF DECLARATIONS 
     DeclExec: Decl -> ProcEnv -> ProcEnv
*)

fun DeclExec (ProcD (pid,fid,cmd)) penv =
       PEnvInsert pid (fid,cmd) penv
|   DeclExec (SeqD(decl1,decl2)) penv =
      let val penv1 = DeclExec decl1 penv
          val penv2 = DeclExec decl2 penv1
       in penv2
      end
|   DeclExec NoDecl penv = penv


(* EXECUTION OF COMMANDS *)

type InputStream = Num list
type OutputStream = Val list
type RunTimeState = Stores * InputStream * OutputStream

(*
CommExec: Comm -> ProcEnv -> RunTimeState -> RunTimeState
*)

fun CommExec SkipC penv state = state
|   CommExec (SeqC(cmd1,cmd2)) penv state =
        let val s = CommExec cmd1 penv state
        in CommExec cmd2 penv s
        end
|   CommExec (IfC(exp,cmd1,cmd2)) penv (state as (stos,_,_)) =
        let val v = ExpEval exp stos
            val cmd = if v = 0 then cmd2
                    else cmd1
        in 
       CommExec cmd penv state
        end
     (* CommExec cmd1 penv state*)
|   CommExec (WhileC(exp,cmd)) penv state =
        CommExec(IfC(exp,SeqC(cmd ,WhileC(exp,cmd)),SkipC)) penv state                
     
|   CommExec (AssignC(id,exp)) penv (stos, inp, outp) =
      let val v = ExpEval exp stos
       in ((StosUpdate id v stos),inp, outp) 
      end
|   CommExec (OutputC exp) penv (stos,inp,outp) =
      let val v = ExpEval exp stos
       in (stos, inp, (v::outp))
      end
|   CommExec (InputC id) penv (stos,[],outp) = raise (EmptyInputStream id)
|   CommExec (InputC id) penv (stos,(i::inp),outp) = 
        let val s =  StosLookup stos id
            val t = if s <> NONE andalso i = 0 then valOf(s) else i
        in
        ((StosUpdate id t stos), inp, outp) 
        end
|   CommExec (ProcCallC (pid,exp)) penv 
                (stos as (global_sto,local_sto), inp, outp) = 
      let val v = ExpEval exp stos
          val (formal,body) = PEnvLookup penv pid
          val call_stores = StosUpdate formal v (global_sto, local_sto)
        in CommExec body penv (StosUpdate formal v call_stores, inp, outp)
      end
|   CommExec (FunCallC (id,pid,exp)) penv 
                (stos as (global_sto,local_sto), inp, outp) = 
      let val v = ExpEval exp stos
          val (formal,body) = PEnvLookup penv pid
          val call_stores =StosUpdate formal v (global_sto, local_sto)
          val (stos' as (global_sto', local_sto'), inp', outp') = 
                 CommExec body penv (call_stores, inp, outp)
        in (StosUpdate id 47 
              (global_sto,local_sto), inp, outp)
      end

(* RUNNING THE PROGRAM *)

fun ProgRun (ProgP(decl,comm)) inp =
       let val penv = DeclExec decl (PEnvInit())
           val (_,_,outp) = CommExec comm penv (([], NONE), inp, [])
         in rev outp
        end
|   ProgRun(ErrorP s) _ = (print ("*** syntax error: "^s^"\n"); [0])

fun Interpret prog inp = ProgRun (parse prog) inp
      handle (EmptyInputStream id) =>
            (print ("*** error: the input stream for "^id^" is empty\n"); [0])
        | (ProcedureNotDeclared x) =>
            (print ("*** error: "^x^" used as procedure but is not declared\n");
            [0])
