package compilation.gbf;
import java.io.*;
import java.util.*;

/* Compilateur de grammaire */

public class Syntax {

final String nomfich_OBJET = "tab_pascal.dat";
DataOutputStream dos;

Liste[][] tab_analyse = new Liste[GBF.max_regles][GBF.max_terminaux];
HashSet[] tab_premier = new HashSet[GBF.max_regles];
HashSet[] tab_suivant = new HashSet[GBF.max_regles];

int i,j;
Liste pointeur;
Liste_prod pointeur2;
int donnee;

/*
---------------------------------------------------------------------
Generateur de TABLE D'ANALYSE SYNTAXIQUE
pour grammaire de type LL.

La grammaire est de type LL
( et permet une analyse descendante predictive ) ssi :
1: X --> Y1 | Y2 | .. | Yk
   Premier(Yi) � Premier(Yj) = � pour i<>j
2: X --> Vide
   Premier(X) � Suivant(X) = �

( Voir plus loin pour la definition des fonctions
  Premier et Suivant )

En pratique la grammaire LL doit etre:
1: Non ambigue (probleme du IF THEN ELSE & des Expressions)
2: Deterministe (factorisee a gauche)
   Ex: Instr = 'ID' ':=' Valeur | 'ID' '(' Liste_Id ')'
       est transformee en:
       Instr    = 'ID' Suite_Id
       Suite_Id = ':=' Valeur | '(' Liste_Id ')'
   Methode generale A --> X Y | X Z  donne:
      A1 --> X A2
      A2 --> Y | Z
3: Non recursive a gauche
   Ex: Liste_Id = Liste_Id ',' 'ID' | 'ID'
       est transformee en:
       Liste_Id1 = 'ID' Liste_Id2
       Liste_Id2 = ',' 'ID' Liste_Id2 | 'Vide'
   Methode generale: A --> A X | Y donne:
      A1 --> Y A2
      A2 --> X A2 | 'Vide'

Pour utiliser ce programme SYNTAXE:

1: Ecrire la grammaire dans le fichier GRAM.DAT
   suivant la syntaxe GBF.
   (syntaxe des Grammaire Bien Formee
   voir plus loin dans le programme)

2: Coder le lexique et les regles
   utilises dans la grammaire
   dans le programme java
   (On utilise pour cela 2 tableaux,
   ne pas oublier les codes 'Vide' & 'Fin')

3: Executer ce programme SYNTAXE,
   si la grammaire est mal formee --> Echec
   si la grammaire n'est pas de type LL
   le programme va planter.
   sinon la table pr�dictive (sous forme inverse)
   est dans le fichier TAB.DAT (file of byte):
   0 | Type (Regle=1\Code=2) , Num correspondant, Liste de productions
----------------------------------------------------------------------
*/

Liste empiler(Liste ptr_pile,
             int type_lex,
             int code_lex,
             Liste_prod ptr_lex)
{
   Liste pointeur;

   pointeur = new Liste();
   pointeur.type_lex = type_lex;
   pointeur.code_lex = code_lex;
   pointeur.ptr_lex = ptr_lex;
   pointeur.suivant = ptr_pile;
   ptr_pile = pointeur;
   return ptr_pile;
}


Liste depiler(Liste ptr_pile)
{
   Liste pointeur;

   if (ptr_pile != null)
   {
      pointeur = ptr_pile.suivant;
      ptr_pile = pointeur;
      return ptr_pile;
   }
   else return null;
}

void affiche_ensemble(HashSet ens)
{
   int k;

   for(k=0; k < GBF.max_terminaux; k ++)
     if (ens.contains(new Integer(k)))  System.out.println(GBF.tab_terminaux[k]);
}

/*
------------------------------------------------------------------------
Fonction PREMIER :

1. Si X --> a alors, mettre a dans p(X)

2. Si X --> A | B alors, p(X) = p(A) + p(B)

3. Si X --> Y1 Y2 .. Yk,  p(X) = p(Y1) + .. p(Yk) exept� le Vide
   quand Vide est dans p(Y1), .. , p(Yk-1)
   Si Vide est dans Y1 � Yk mettre Vide dans X
------------------------------------------------------------------------
*/

void premier(HashSet ens,
             Liste pointeur,
             boolean option)
{
   switch (pointeur.type_lex) {
   case GBF.type_terminal : {
                 /* Regle1 */
                 boolean res = ens.add(new Integer(pointeur.code_lex));

                 /* Regle2 */
                 if (option)
                 {
                    while (!( (pointeur == null)
                    || (pointeur.type_lex == GBF.type_barre) ))
                       pointeur = pointeur.suivant;

                    if (!( pointeur == null ))
                    {
                       pointeur = pointeur.suivant;
                       premier(ens, pointeur, true);
                    }
                 }
              }
              break;

   case GBF.type_regle : {
                 /* Regle3 */
                 premier(ens, GBF.tab_gram[pointeur.code_lex], true);

                 if (ens.contains(new Integer(GBF.code_pos("Vide"))))
                 {
                    boolean res = ens.remove(new Integer(GBF.code_pos("Vide")));
                    pointeur = pointeur.suivant;
                    if (pointeur == null)  res = ens.add(new Integer(GBF.code_pos("Vide")));
                    else premier(ens,pointeur,false);
                 }

                 /* Regle2 */
                 if (option)
                 {
                    while (!( (pointeur == null)
                    || (pointeur.type_lex == GBF.type_barre) ))
                       pointeur = pointeur.suivant;

                    if (!( pointeur == null ))
                    {
                       pointeur = pointeur.suivant;
                       premier(ens,pointeur,true);
                    }
                 }
              }
              break;
   }
}


/*
-------------------------------------------------------------------------
Fonction SUIVANT :

1: Mettre Fin dans s(S), ou S est l'GBF.axiome et Fin
   le marqueur indiquant la fin du texte source

2: A --> X B Y alors s(B):=s(B)+p(Y) excepte le Vide

3: A --> X B   ou   A --> X B Y et Vide dans p(Y) alors,
   s(B):=s(B)+s(A)
-------------------------------------------------------------------------
*/

void suivant(HashSet ens, int code_lex)
{
   int i;
   boolean res;
   Liste pointeur;

   // System.out.println("suivant1");

   /* Regle1 */
   if (code_lex == GBF.axiome)  {
   	if (ens != null) ens.clear();
   	res = ens.add(new Integer(GBF.code_pos("Fin")));
   }

   // System.out.println("suivant2");

   for( i=0; i < GBF.max_regles; i ++)
   {
      pointeur = GBF.tab_gram[i];
      

      while (pointeur != null)
      {
         // System.out.println("suivant3");
         
         while (!((pointeur == null) 
               || ((pointeur.type_lex == GBF.type_regle) && (pointeur.code_lex == code_lex)) ))
            pointeur = pointeur.suivant;

         // System.out.println("suivant4");
         
         if (pointeur != null)
         {
            do {
               // System.out.println("suivant5");	
               pointeur = pointeur.suivant;
               // System.out.println("suivant6");	
               res = ens.remove(new Integer(GBF.code_pos("Vide")));
               // System.out.println("suivant7");	

	       if (pointeur != null)
	       	
               switch (pointeur.type_lex) {
                  case GBF.type_terminal : res = ens.add(new Integer(pointeur.code_lex)); break;
                  case GBF.type_regle    : {
                  	Iterator it = tab_premier[pointeur.code_lex].iterator();
                  	Integer element;
                  	while (it.hasNext()) {
                           element = (Integer) it.next();
                           res = ens.add(element);
                        }
                        // ens = ens + tab_premier[pointeur.code_lex];
                 	break;
                  }
               }
               // System.out.println("suivant8");	
               
            } while (ens.contains( new Integer(GBF.code_pos("Vide")) ));

            res = ens.remove(new Integer(GBF.code_pos("Vide")));

            if ( (pointeur == null) || (pointeur.type_lex == GBF.type_barre) )
               if (! (i == code_lex))
                  if (i < code_lex) {
                     Iterator it = tab_suivant[i].iterator();
                     Integer element;
                     while (it.hasNext()) {
                        element = (Integer) it.next();
                        res = ens.add(element);
                     }
                     // ens=ens+tab_suivant[i];
                  }
                  else suivant(ens,i);
         }
      }
   }
}

/*
------------------------------------------------------------------------
Construction de la TABLE D'ANALYSE :

Chaque regle est du type X --> Y1 | Y2 | .. | Yk
et 'a' represente un code.

1: Pour chaque X --> Yi (regle X reduite a sa partie i)
   proc�der aux �tapes 2 et 3.

2: Pour chaque a dans p(Yi),
   ajouter X --> Yi � Tab_Analyse[X,a]

3: si Vide dans p(Yi),
   pour chaque a dans s(X) ajouter X --> Yi � Tab_Analyse[X,a]
   et si Fin     dans s(X) ajouter X --> Yi � Tab_Analyse[X,Fin]

4: Chaque entree non definie de Table est une Erreur
-------------------------------------------------------------------------
*/

void finalruire_table()
{
   Liste pointeur;
   HashSet ens;
   int x,a;

   /* Initialisation */
   for( x=0; x < GBF.max_regles; x ++) {
     for( a=0; a < GBF.max_terminaux; a ++) {
       tab_analyse[x][a]=null;
     }
   }

   for( x=0; x < GBF.max_regles; x ++)
   {
      pointeur = GBF.tab_gram[x];

      while (pointeur != null)
      {
         ens = new HashSet();
         premier(ens,pointeur,false);

         for(a=0; a < GBF.max_terminaux; a ++) {
            if (ens.contains(new Integer(a)))  tab_analyse[x][a] = pointeur;
         }

         if (ens.contains(new Integer(GBF.code_pos("Vide"))))
         {
            if (tab_suivant[x].contains(new Integer(GBF.code_pos("Vide"))))
               tab_analyse[x][GBF.code_pos("Fin")] = pointeur;

            for(a=0; a < GBF.max_terminaux; a ++) {
               if (tab_suivant[x].contains(new Integer(a)))  tab_analyse[x][a] = pointeur;
            }
         }

         while (!( (pointeur == null) || (pointeur.type_lex == GBF.type_barre) )) {
            pointeur = pointeur.suivant;
         }
         if (! (pointeur == null))  pointeur = pointeur.suivant;
      }
   }
}

void affiche_table()
{
   int i,j;
   Liste pointeur;

   for( i=0; i < GBF.max_regles; i ++)
   {
     for( j=0; j < GBF.max_terminaux; j ++)
     {
        pointeur = tab_analyse[i][j];
        System.out.println("Tab[" +  GBF.tab_regles[i] + "," + GBF.tab_terminaux[j] + "] >");
        while (! ((pointeur == null) || (pointeur.type_lex == GBF.type_barre)))
        {
           if (pointeur.type_lex == GBF.type_regle)
                System.out.println(GBF.tab_regles[pointeur.code_lex] + " ");
           else System.out.println(GBF.tab_terminaux[pointeur.code_lex] + " ");
           System.out.println(GBF.affiche_prod(pointeur.ptr_lex));
           pointeur = pointeur.suivant;
        }
     }
   }
}

public Syntax()
{
   int i;

   try {

   dos = new DataOutputStream(new FileOutputStream(nomfich_OBJET));

   System.out.println("1. Etude et Codage de la Grammaire >");
   GBF gbf = new GBF(); // compile_gbf

   System.out.println("2. Etude de la Fonction Premier >");
   for( i=0; i < GBF.max_regles; i ++)
   {
      tab_premier[i] = new HashSet();
      premier(tab_premier[i],GBF.tab_gram[i],true);
      // System.out.println(Tab_regles[i]);
      // affiche_ensemble(Tab_Premier[i]);
   }

   System.out.println("3. Etude de la Fonction Suivant >");
   for( i=0; i < GBF.max_regles; i ++)
   {
      // System.out.println("i =" + i);
      tab_suivant[i] = new HashSet();
      suivant(tab_suivant[i],i);
   }

   System.out.println("4. Construction de la table d'analyse predictive >");
   finalruire_table();
   // affiche_table();

   /* Sauvegarde de la table inverse: */

   for( i=0; i < GBF.max_regles; i ++)
   {
     for( j=0; j < GBF.max_terminaux; j ++)
     {
        pointeur = tab_analyse[i][j];
        GBF.ptr_pile = null;

        /* Inversion de la table en utilisant une pile */
        
        while (!( (pointeur == null) || (pointeur.type_lex == GBF.type_barre) ))
        {
           
           GBF.ptr_pile = empiler(GBF.ptr_pile, pointeur.type_lex,
                            pointeur.code_lex,
                            pointeur.ptr_lex);
           pointeur = pointeur.suivant;
        }
                
        while (! (GBF.ptr_pile == null))
        {
           donnee = GBF.ptr_pile.type_lex;
           dos.writeByte((byte) donnee);

           donnee = GBF.ptr_pile.code_lex;
           dos.writeByte((byte) donnee+1);

           pointeur2 = GBF.ptr_pile.ptr_lex;
           while (! (pointeur2 == null))
           {
              donnee = pointeur2.prod_lex;
              dos.writeByte((byte) donnee);
              pointeur2 = pointeur2.suivant;
           }
           donnee = 0;
           dos.writeByte((byte) donnee);

           GBF.ptr_pile = depiler(GBF.ptr_pile);
        }

        donnee = 0;
        dos.writeByte((byte) donnee);
     }
   }

   System.out.println("Succes");
   dos.close();

   }
   catch (Exception e) {
      System.out.println("Exception " + e);
   }

}

static public void main(String[] args) {
   Syntax syntax = new Syntax();
}

}