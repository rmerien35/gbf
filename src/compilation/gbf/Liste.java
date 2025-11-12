package compilation.gbf;

public class Liste {
   /* liste des termes de la regle */
   int type_lex;     /* 1 -> Regle , 2 -> Terminal , 3 -> |  */
   int code_lex;     /* Numero de la regle\du terminal       */
   Liste_prod ptr_lex = null;  /* Pointeur sur la liste de productions */
   Liste suivant = null;

   public Liste() {
   }
}

