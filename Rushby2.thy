theory Rushby
imports Main
begin

typedecl u -- "U_beings"

consts "g" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold>>" 54)
consts "k" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold><" 54)
consts "e" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold>=" 54)

abbreviation Greater0 where
  "Greater0 \<equiv> \<forall> x y. x \<^bold>> y \<or> y \<^bold>> x \<or> x \<^bold>= y" 

abbreviation God :: "u\<Rightarrow>bool" ("G") where 
  "G \<equiv> \<lambda>x.  \<not>(\<exists> y. (y \<^bold>> x))"

consts "re" :: "u \<Rightarrow> bool"

abbreviation ExUnd where
  "ExUnd \<equiv> \<exists> x . God x"

abbreviation Greater1 where 
  "Greater1 \<equiv> \<forall> x . (\<not>re x) \<longrightarrow> (\<exists> y . y \<^bold>> x)" 

theorem "God!":
  assumes ExUnd 
  assumes "Greater1"
  shows "\<exists> x. (G x \<and> re x)"
(*sledgehammer*)
using assms by blast

abbreviation Greater2 where
  "Greater2 \<equiv> (\<forall> x y. (re x \<and> \<not> re y) \<longrightarrow> (x \<^bold>> y))"

abbreviation "Ex_re" where
  "Ex_re \<equiv> \<exists> x. re x"

theorem "God!2":
  assumes ExUnd 
  assumes "Greater2" and "Ex_re"
  shows "\<exists> x. (G x \<and> re x)"
(*sledgehammer*)
using assms by blast

abbreviation "P1" where
  "P1 \<equiv> \<exists> x. G x"

theorem "P1!":
  assumes ExUnd
  shows P1 using assms by -

consts "P" :: "(u \<Rightarrow> bool) \<Rightarrow> bool" -- "greater making property"

abbreviation "P_re" where
  "P_re \<equiv> P re"

abbreviation "subsetP" where
  "subsetP \<equiv> \<lambda> FF. \<forall>x. FF x \<longrightarrow> P x"

abbreviation "Greater3" where
  "Greater3 \<equiv> \<forall> x y . x \<^bold>> y \<longleftrightarrow> ((\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y)))"

abbreviation "Realization" where
  "Realization \<equiv> \<forall> FF. subsetP FF \<longrightarrow> (\<exists>x. \<forall>f. P f \<longrightarrow> (f x \<longleftrightarrow> FF f))"
(*  "Realization \<equiv> \<forall> FF \<subseteq> {x . P x} . \<exists>x. \<forall>f. f(x) \<longleftrightarrow> f \<in> FF"*)

abbreviation aG where
  "aG \<equiv> \<lambda>x . \<forall>y. x \<^bold>> y"

abbreviation ExUndA where
  "ExUndA \<equiv> \<exists>x. aG x"

theorem "God!3":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUndA
  shows "\<exists> x. (aG x \<and> re x)" 
proof -
    from assms(4) have "\<exists>x. aG x" by -
    moreover {
      fix x
      assume gx: "aG x"
      then have "\<forall> y. (x \<^bold>> y)" by -
      from this assms(2) have "\<forall>y.(\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y))" by blast
      from this assms(1) have rx: "re x" by blast
      from gx rx have "aG x \<and> re x" by (rule conjI)
      hence "\<exists> x. (aG x \<and> re x)" by (rule exI)
    }
    ultimately show ?thesis by (rule exE)
qed

theorem "GodCanDoItAll":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUndA
  shows "\<forall>f. P f \<longrightarrow> (\<exists>x. aG x \<and> f x)"
proof -
  {
    fix f
    assume "P f"
    from assms(4) have "\<exists>x. aG x" by -
    moreover {
      fix x
      assume gx: "aG x"
      from this assms(2) assms(3) have "\<forall> y. x \<^bold>> y" by blast
      from this assms(2) have "\<forall>y.(\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y))" by blast
      from this assms(1) have rx: "f x" by blast
      from gx rx have "aG x \<and> f x" by (rule conjI)
      hence "\<exists> x. (aG x \<and> f x)" by (rule exI)
    }
    ultimately have "(\<exists>x. aG x \<and> f x)" by (rule exE)
  }
  thus ?thesis by blast
qed

consts D :: "(u \<Rightarrow> bool) \<Rightarrow> bool"

axiomatization where
  dsubstP: "\<forall>f. D f \<longrightarrow> P f"

(* do not further consider quasi id, because we have a different proof *)
abbreviation quasi_id where
  "quasi_id \<equiv> \<lambda>x y. \<forall>f. P f \<and> \<not>D f \<longrightarrow> f x = f y"

abbreviation Realization_W where
  "Realization_W \<equiv> \<forall> FF. subsetP FF \<longrightarrow> (\<exists>x. \<forall>f. FF f \<longrightarrow> f x)"

end