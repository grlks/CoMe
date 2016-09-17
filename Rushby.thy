theory Rushby
imports Main
begin

typedecl u -- "U_beings"

consts "g" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold>>" 54)
consts "k" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold><" 54)
consts "e" :: "u \<Rightarrow> u \<Rightarrow> bool" (infixr "\<^bold>=" 54)

axiomatization where
  Gr: "\<forall> x y. x \<^bold>> y \<or> y \<^bold>> x \<or> x \<^bold>= y" 

abbreviation God :: "u\<Rightarrow>bool" ("God") where 
  "God \<equiv> \<lambda>x.  \<not>(\<exists> y. (y \<^bold>> x))"

consts "re" :: "u \<Rightarrow> bool"

axiomatization where
  ExUnd: "\<exists> x . God x"

abbreviation Greater1 where 
  "Greater1 \<equiv> \<forall> x . (\<not>re x) \<longrightarrow> (\<exists> y . y \<^bold>> x)" 

theorem "God!": 
  assumes "Greater1"
  shows "\<exists> x. (God x \<and> re x)"
(*sledgehammer*)
using ExUnd assms by blast

abbreviation Greater2 where
  "Greater2 \<equiv> (\<forall> x y. (re x \<and> \<not> re y) \<longrightarrow> (x \<^bold>> y))"

abbreviation "Ex_re" where
  "Ex_re \<equiv> \<exists> x. re x"

theorem "God!2": 
  assumes "Greater2" and "Ex_re"
  shows "\<exists> x. (God x \<and> re x)"
(*sledgehammer*)
using ExUnd assms(1) assms(2) by blast

abbreviation "P1" where
  "P1 \<equiv> \<exists> x. God x"

theorem "P1" using ExUnd by -

consts "P" :: "(u \<Rightarrow> bool) \<Rightarrow> bool" -- "greater making property"

abbreviation "P_re" where
  "P_re \<equiv> P re"

abbreviation "subsetP" where
  "subsetP \<equiv> \<lambda> FF. \<forall>x. FF x \<longrightarrow> P x"

abbreviation "Greater3" where
  "Greater3 \<equiv> \<forall> x y . x \<^bold>> y \<longleftrightarrow> (\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y)) "


abbreviation "RealizationA" where
  "RealizationA \<equiv> \<forall> FF. subsetP FF \<longrightarrow> (\<exists>x. \<forall>f. P f \<longrightarrow> (f x \<longleftrightarrow> FF f))"

abbreviation "Realization" where
  "Realization \<equiv> \<forall> FF. \<exists>x. \<forall>f. P f \<longrightarrow> (f x \<longleftrightarrow> FF f)"
(*  "Realization \<equiv> \<forall> FF \<subseteq> {x . P x} . \<exists>x. \<forall>f. f(x) \<longleftrightarrow> f \<in> FF"*)

theorem "God!3":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUnd
  shows "\<exists> x. (God x \<and> re x)"
proof -
  have "\<exists> x. God x" using ExUnd by -
  moreover {
    fix x
    assume 0: "God x"
    have "re x" proof (cases "re x")
      assume "re x"
      thus ?thesis by simp
    next
      assume cas: "\<not>(re x)"
      {
        fix ff
        assume ass:"(\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> ff f)) \<and>  ff re"
        from this have 1: "\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> ff f)" by simp
        from ass have 3: "ff re" by simp
        from 1 3 assms(3) have "\<exists>y. \<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> ff f)" by blast
        moreover {
          fix y
          assume 4: "\<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> ff f)"
          from this 3 assms(1) have "re y" by blast
          from 4 0 have a:"\<not> (y \<^bold>> x)" by blast
          from 1 4 have vor1: "\<forall>F. P F \<longrightarrow> (F x \<longrightarrow> F y)" by blast
          from assms(1) 3 4 cas have "P re \<and> re y \<and> \<not>(re x)" by blast
          hence vor2: "\<exists>F. P F \<and> (F y \<and> \<not>F x)" by blast
          from vor1 vor2 assms(2) have "y \<^bold>> x" by blast
          from this a have False by simp
        }
        ultimately have False by (rule exE)
      }
      hence False by blast
      thus ?thesis by simp
    qed
    from 0 this have "God x \<and> re x" by (rule conjI)
    hence "\<exists>x. God x \<and> re x" by (rule exI)
  }
  ultimately show ?thesis by (rule exE)
qed


end