package compilation.gbf;
import java.io.*;

/* Interpreteur pour Machine � Pile */

public class GBF {

static final int type_echec = -1;

static final int type_regle = 1;
static final int type_terminal = 2;

static final int type_barre = 3;
static final int type_separ = 4;
static final int type_affect = 5;
static final int type_fin = 6;
static final int type_vide = 7;
static final int axiome = 0;
int type_lex,code_lex,prod_lex;

final String nomfich_SOURCE = "gram_pascal.dat";
static final int max_terminaux = 38;
static final int max_regles = 26;

static final String[] tab_terminaux = {
"VAR"     ,  "BEGIN"  ,  "END"    ,  "IF"       ,  "THEN"    ,
"ELSE"    ,  "WHILE"  ,  "DO"     ,  "FUNCTION" ,  "WRITE"   ,
"READ"    ,  "NOT"   ,   "OR"     ,  "AND"      ,  "INTEGER" ,
"STRING"  ,  "VOID"  ,   "RETURN" ,  ":="       ,  "CH"      ,
"NB"      ,  "ID"    ,   "Fin"    ,  "Vide"     ,  "<"       ,
">"       ,  "="     ,   "+"      ,  "-"        ,  "*"       ,
"/"       ,  "("     ,   ")"      ,  ";"        ,  ","       ,
":"       ,  "."     ,   "NEG"    };

static final String[] tab_regles = {
"Prog"        ,  "Declar"      ,  "Liste_Id1"   ,  "Liste_Id2"  ,
"Type"        ,  "Fonct"       ,  "En_Tete"     ,  "Type_Fonct" ,
"Liste_Param" ,  "Instr_Comp"  ,  "Liste_Instr" ,  "Instr"      ,
"Suite_Id1"   ,  "Valeur"      ,  "Expr1"       ,  "Expr2"      ,
"Simple1"     ,  "Simple2"     ,  "Terme1"      ,  "Terme2"     ,
"Facteur"     ,  "Suite_Id2"   ,  "Op_Relat"    ,  "Op_Add"     ,
"Op_Mult"     ,  "Production"  };

/*
final String nomfich_SOURCE = "gram_gbf.dat";
static final int max_terminaux = 7;
static final int max_regles = 4;

static final String[] tab_terminaux = {
"Regle"  ,  "Code"  ,  "Barre"  ,  "Separ"  ,  "Affect",
"Fin"    ,  "Vide"};

static final String[] tab_regles = {
"Expr"  ,  "Partie1"  ,  "Partie2"  ,  "Terme"};
*/

static Liste_prod ptr_lex;
static Liste ptr_pile, ptr_gram;
static Liste[] tab_gram = new Liste[max_regles];

File fichier_SOURCE;
DataInputStream dis;
RandomAccessFile raf;
DataOutputStream dos;

int pos_fichier;
String chaine;
// boolean erreur;

static int code_pos(String chaine)
{
   int i;
   int code_pos_result = -1;

   i=max_terminaux-1;
   while (! ((chaine.equals(tab_terminaux[i])) || (i==0)))  i=i-1;

   code_pos_result = i;
   return code_pos_result;
}

static int regle_pos(String chaine)
{
   int i;
   int regle_pos_result = -1;

   i=max_regles-1;
   while (! ((chaine.equals(tab_regles[i])) || (i==0)))  i=i-1;

   regle_pos_result = i;
   return regle_pos_result;
}

static String affiche_prod(Liste_prod ptr_lex)
{
   Liste_prod pointeur;
   String ch1,ch2;

   String affiche_prod_result;
   ch1=" ";
   pointeur=ptr_lex;
   while (! (pointeur==null))
   {
      ch2 = String.valueOf( (int) pointeur.prod_lex);
      ch1=ch1+"%"+ch2+" ";
      pointeur=pointeur.suivant;
   }
   affiche_prod_result=ch1;
   return affiche_prod_result;
}

/* ---------------------- Analyse Lexicale -------------------------- */

boolean lettre(char car)
/* lettre -> A..Z | a..z | _ */
{
   boolean lettre_result;

   if ( ((car>='A') && (car<='Z'))
	|| ((car>='a') && (car<='z'))
	|| (car == '_') ) lettre_result=true;
   else lettre_result=false;

   return lettre_result;
}

boolean chiffre(char car)
/* chiffre -> decimal */
{
   boolean chiffre_result;
   switch (car) {
      case '0': case '1': case '2': case '3': case '4' : case '5':
      case '6': case '7': case '8': case '9': chiffre_result=true;
      break;

      default: chiffre_result = false;
   }
   return chiffre_result;
}

boolean signe(char car)
/* Signe -> + | - */
{
   boolean signe_result;
   switch (car) {
      case '+':case '-' : signe_result=true; break;
      default:      signe_result=false;
   }
   return signe_result;
}

// boolean blanc(int pos_fichier) throws IOException
boolean blanc() throws IOException
/* blanc -> #32 | #10 | #13 */
{
   char car;
   boolean blanc_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      switch (car) {
         case '\40':
         case '\12':
         case '\15': {pos_fichier=pos_fichier+1; blanc_result=true;} break;

         default: blanc_result=false;
      }
   }
   catch (IOException ioe) {
      throw ioe;
   }

   return blanc_result;
}

boolean car_affect() throws IOException
/* Affect -> = */
{
   char car;
   boolean car_affect_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      switch (car) {
      case '=': {
              pos_fichier = pos_fichier + 1;
              car_affect_result = true;
           }
           break;
      default: car_affect_result = false;
      }
   }
   catch (IOException ioe) {
         throw ioe;
   }

   return car_affect_result;
}

boolean car_barre() throws IOException
/* Barre -> | */
{
   char car;
   boolean car_barre_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      switch (car) {
      case '|': {
              pos_fichier=pos_fichier+1;
              car_barre_result=true;
           }
           break;
      default: car_barre_result=false;
      }
   }
   catch (IOException ioe) {
            throw ioe;
   }

   return car_barre_result;
}

boolean car_separ() throws IOException
/* Separ -> ; */
{
   char car;
   boolean car_separ_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      switch (car) {
      case ';': {
              pos_fichier = pos_fichier + 1;
              car_separ_result = true;
           }
           break;
      default: car_separ_result = false;
      }
   }
   catch (IOException ioe) {
      throw ioe;
   }

   return car_separ_result;
}

boolean prod2() throws IOException
/* Prod2 -> Chiffre Prod2 | vide */
{
   char car;
   boolean prod2_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (chiffre(car))
      {
        pos_fichier = pos_fichier + 1;
        chaine = chaine + car;
        if (chaine.length()<=3)  prod2_result = prod2();
        else prod2_result = false;
      }
      else prod2_result = true;
   }
   catch (IOException ioe) {
      throw ioe;
   }

   return prod2_result;
}

boolean prod1() throws IOException
/* Prod1 -> % Prod2 */
{
   char car;
   boolean prod1_result;
   chaine="";

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (car=='%')
      {
         pos_fichier = pos_fichier + 1;
         prod1_result = prod2();
      }
      else prod1_result=false;
   }
   catch (IOException ioe) {
      throw ioe;
   }

   // if (prod1_result == true) System.out.println("prod = " + chaine);
   return prod1_result;
}

// boolean id2(int pos_fichier, String chaine) throws IOException
boolean id2() throws IOException
/* id2 -> lettre id2 | chiffre id2 | vide */
{
   char car;
   boolean id2_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (lettre(car) || chiffre(car))
      {
         pos_fichier = pos_fichier + 1;
         chaine = chaine + car; // Character.toUpperCase(car);

         if (chaine.length() <= 16)  id2_result = id2(); // id2(pos_fichier,chaine);
         else id2_result = false;
      }
      else id2_result = true;
   }
   catch (IOException ioe) {
      throw ioe;
   }

   return id2_result;
}

// boolean id1(int pos_fichier, String chaine) throws IOException
boolean id1() throws IOException
/* id1 -> lettre id1 */
{
   char car;
   boolean id1_result;
   chaine="";

   // System.out.println("id1 : pos_fichier = " + pos_fichier);
   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (lettre(car))
      {
         pos_fichier = pos_fichier + 1;
         chaine = chaine + car; // Character.toUpperCase(car);
         id1_result = id2(); // id2(pos_fichier,chaine);
      }
      else id1_result = false;
   }
   catch (IOException ioe) {
      throw ioe;
   }

   // if (id1_result == true) System.out.println("chaine = " + chaine);
   return id1_result;
}

boolean chaine1() throws IOException
/* chaine1 -> ' car ' */
{
   char car;
   int sortie;
   boolean chaine1_result;
   chaine = "";

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (car=='\47')
      {
         sortie=0;
         do {
            pos_fichier=pos_fichier+1;
            raf.seek(pos_fichier);
            car = (char) raf.readUnsignedByte();

            if (car == '\47')  sortie = 1;
            else if (chaine.length() == 255) sortie = 2;
            else chaine = chaine + car;
         } while (!( sortie != 0));

         pos_fichier = pos_fichier + 1;
         if (sortie == 1)  chaine1_result = true;
         else chaine1_result = false;
      }
      else chaine1_result = false;
   }
   catch (IOException ioe) {
      throw ioe;
   }

   // if (chaine1_result == true) System.out.println("chaine = " + chaine);
   return chaine1_result;
}

// boolean commentaire(int pos_fichier) throws IOException
boolean commentaire() throws IOException
/*
   commentaire -> { car }
                 #123 car #125
   = parenthese
 */
{
   char car;
   int sortie;
   boolean parenthese_result;

   try {
      raf.seek(pos_fichier);
      car = (char) raf.readUnsignedByte();

      if (car == '{')
      {
         sortie=0;
         do {
            pos_fichier = pos_fichier + 1;
            raf.seek(pos_fichier);
            car = (char) raf.readUnsignedByte();

            if (car == '}')  sortie = 1;
         } while (!(sortie != 0));

         pos_fichier = pos_fichier + 1;
         if (sortie == 1)  parenthese_result = true;
         else parenthese_result = false;
      }
      else parenthese_result = false;
   }
   catch (IOException ioe) {
      sortie = 2;
      throw ioe;
   }

   return parenthese_result;
}

void production()
{
   int erreur;
   Liste_prod pointeur;

   try {

   while (blanc() || commentaire());
   if (prod1())
   {
      ptr_lex = new Liste_prod();
      pointeur = ptr_lex;
      pointeur.prod_lex = Integer.parseInt(chaine); // val(chaine,pointeur.prod_lex,erreur);

      while (blanc() || commentaire());
      while (prod1())
      {
         pointeur.suivant = new Liste_prod();
         pointeur = pointeur.suivant;
         pointeur.prod_lex = Integer.parseInt(chaine); // val(chaine,pointeur.prod_lex,erreur);

         while (blanc() || commentaire());
      }
      pointeur.suivant = null;
   }
   else ptr_lex = null;

   }
   catch(Exception e) {
      System.out.println(e);
   }
}

void affiche_lex()
{
   switch (type_lex) {
      case type_echec   : System.out.print("Echec"); break;
      case type_regle   : System.out.print(tab_regles[code_lex] + affiche_prod(ptr_lex));  break;
      case type_terminal: System.out.print(tab_terminaux[code_lex] + affiche_prod(ptr_lex)); break;
      case type_barre   : System.out.print("| " ); break;
      case type_separ   : System.out.println("; "); break;
      case type_affect  : System.out.print("= "); break;
      case type_fin     : System.out.println("Fin"); break;
   }
}

void lex()
{
   try {
      while (blanc() || commentaire());
      // System.out.println("pos_fichier = " + pos_fichier);

      if (id1()) {
         type_lex = type_regle;
         code_lex = regle_pos(chaine);
         production();
      }
      else if (chaine1()) {
         type_lex = type_terminal;
         code_lex = code_pos(chaine);
         production();
      }
      else if (car_affect())   type_lex = type_affect;
      else if (car_barre())    type_lex = type_barre;
      else if (car_separ())    type_lex = type_separ;
      else type_lex = type_echec;
      // System.out.println("type_lex = " + type_lex);
   }
   catch (IOException ioe) {
      type_lex = type_fin;
   }

   affiche_lex();
}

/* ------------ Analyse Syntaxique & Production du Code ------------- */

void prod_1()
{
   /* Initialiser Tab_Gram[regle] */
   tab_gram[code_lex] = new Liste();
   ptr_gram = tab_gram[code_lex];
}

void prod_2()
{
   /* Avancer le pointeur */
   ptr_gram.suivant = new Liste();
   ptr_gram = ptr_gram.suivant;
}

void prod_3()
{
   /* produire le terme */
   ptr_gram.type_lex = type_lex;
   ptr_gram.code_lex = code_lex;
   ptr_gram.ptr_lex = ptr_lex;
}

void prod_4()
{
   /* Produire la barre */
   ptr_gram.type_lex = type_lex;
   ptr_gram.code_lex = 0;
   ptr_gram.ptr_lex = null;
}

void prod_5()
{
   /* produire null */
   ptr_gram.suivant = null;
}

// -------------------------------------------------------------------------------


void produire_code()
{
   Liste_prod pointeur;

   pointeur = ptr_pile.ptr_lex;
   while (! (pointeur == null))
   {
      switch (pointeur.prod_lex) {
         case 1: prod_1(); break;
         case 2: prod_2(); break;
         case 3: prod_3(); break;
         case 4: prod_4(); break;
         case 5: prod_5(); break;
      }

      pointeur=pointeur.suivant;
   }
}

boolean expr()
{
   boolean expr_result;
   switch (type_lex) {
      case type_regle : {
                      prod_1();
                      lex();
                      if (type_lex == type_affect)
                      {
                         lex();
                         if (partie1())
                         {
                            lex();
                            expr_result = expr();
                         }
                         else expr_result = false;
                      }
                      else expr_result = false;
                   }
                   break;
      case type_fin   : expr_result = true; break;
      default:          expr_result = false;
   }
   return expr_result;
}

boolean partie1()
{
   boolean partie1_result;
   if (terme())
   {
      prod_3();
      lex();
      partie1_result = partie2();
   }
   else partie1_result = false;
   return partie1_result;
}

boolean partie2()
{
   boolean partie2_result;
   switch (type_lex) {
      case type_barre : {
                      prod_2();
                      prod_4();
                      prod_2();
                      lex();
                      partie2_result = partie1();
                   }
                   break;
      case type_regle:
      case type_terminal: if (terme())
                   {
                      prod_2();
                      prod_3();
                      lex();
                      partie2_result = partie2();
                   }
                   else partie2_result = false;
                   break;
      case type_separ : {
                      prod_5();
                      partie2_result = true;
                   }
                   break;
      default:         partie2_result = false;
   }
   return partie2_result;
}

boolean terme()
{
   boolean terme_result;
   switch (type_lex) {
      case type_regle:
      case type_terminal : terme_result = true; break;
      default:             terme_result = false;
   }
   return terme_result;
}

void affiche_gram()
{
   int i;
   Liste pointeur;

   System.out.println("Grammaire > ");
   for( i=0; i < max_regles; i ++)
   {
      pointeur = tab_gram[i];
      System.out.println(tab_regles[i] + " = ");

      while (!( pointeur == null))
      {
         switch (pointeur.type_lex) {
            case type_regle : {
                            System.out.println(tab_regles[pointeur.code_lex]);
                            System.out.println(affiche_prod(pointeur.ptr_lex));
                         }
                         break;
            case type_terminal : {
                              System.out.println(tab_terminaux[pointeur.code_lex]);
                              System.out.println(affiche_prod(pointeur.ptr_lex));
                            }
                            break;
            case type_barre : System.out.println("| "); break;
         }
         pointeur = pointeur.suivant;
      }
      System.out.println(";");
   }
}

public GBF()
{
   try {
      fichier_SOURCE = new File(nomfich_SOURCE);
      raf = new RandomAccessFile(fichier_SOURCE,"r");
      pos_fichier=0;

      System.out.println("Grammaire Bien Formee >");
      lex();

      if (expr())  System.out.println("Succes");
      else 	   System.out.println("Erreur");

      raf.close();
   }
   catch (Exception e) {
      System.out.println("Exception " + e);
   }
}

static public void main(String[] args) {
   GBF gbf = new GBF();
}

}