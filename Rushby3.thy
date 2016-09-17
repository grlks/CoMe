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
  "Greater3 \<equiv> \<forall> x y . x \<^bold>> y \<longleftrightarrow> (\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y)) "

abbreviation "Realization" where
  "Realization \<equiv> \<forall> FF. subsetP FF \<longrightarrow> (\<exists>x. \<forall>f. P f \<longrightarrow> (f x \<longleftrightarrow> FF f))"
(*  "Realization \<equiv> \<forall> FF \<subseteq> {x . P x} . \<exists>x. \<forall>f. f(x) \<longleftrightarrow> f \<in> FF"*)

abbreviation Allah where
  "Allah \<equiv> \<lambda>x . \<forall>y. x \<^bold>> y"

abbreviation ExUndAllah where
  "ExUndAllah \<equiv> \<exists>x. Allah x"

theorem "Allah!3":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUndAllah
  shows "\<exists> x. (Allah x \<and> re x)" 
proof -
    from assms(4) have "\<exists>x. Allah x" by -
    moreover {
      fix x
      assume gx: "Allah x"
      then have "\<forall> y. (x \<^bold>> y)" by -
      from this assms(2) have "\<forall>y.(\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y))" by blast
      from this assms(1) have rx: "re x" by blast
      from gx rx have "Allah x \<and> re x" by (rule conjI)
      hence "\<exists> x. (Allah x \<and> re x)" by (rule exI)
    }
    ultimately show ?thesis by (rule exE)
qed

theorem "AllahCanDoItAll":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUndAllah
  shows "\<forall>f. P f \<longrightarrow> (\<exists>x. Allah x \<and> f x)"
proof -
  {
    fix f
    assume "P f"
    from assms(4) have "\<exists>x. Allah x" by -
    moreover {
      fix x
      assume gx: "Allah x"
      from this assms(2) assms(3) have "\<forall> y. x \<^bold>> y" by blast
      from this assms(2) have "\<forall>y.(\<forall>F. P F \<longrightarrow> (F y \<longrightarrow> F x)) \<and> (\<exists>F. P F \<and> (F x \<and> \<not>F y))" by blast
      from this assms(1) have rx: "f x" by blast
      from gx rx have "Allah x \<and> f x" by (rule conjI)
      hence "\<exists> x. (Allah x \<and> f x)" by (rule exI)
    }
    ultimately have "(\<exists>x. Allah x \<and> f x)" by (rule exE)
  }
  thus ?thesis by blast
qed


theorem "God!3":
  assumes P_re:
          P_re
  assumes Greater3:
          Greater3
  assumes Realization:
          Realization
  assumes ExUnd:
          ExUnd
  shows "\<exists> x. (God x \<and> re x)"
proof -
  {
    fix x
    assume 0: "God x"
    have "re x" proof (cases "re x")
      assume "re x"
      thus ?thesis by -
    next
      assume cas: "\<not>(re x)"
      have "\<exists>ff. (\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> ff f)) \<and>  ff re" by blast
      moreover {
        fix ff
        assume ass:"(\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> ff f)) \<and>  ff re"
        from this have 1: "\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> ff f)" by simp
        from ass have 3: "ff re" by simp
        from 0 1 Greater3 Realization have "\<exists>y. \<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> ff f)"  by metis
        moreover {
          fix y
          assume 4: "\<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> ff f)"
          from this 3 P_re have "re y" by blast
          from 4 0 have a:"\<not> (y \<^bold>> x)" by blast
          from 1 4 have vor1: "\<forall>F. P F \<longrightarrow> (F x \<longrightarrow> F y)" by blast
          from P_re 3 4 cas have "P re \<and> re y \<and> \<not>(re x)" by blast
          hence vor2: "\<exists>F. P F \<and> (F y \<and> \<not>F x)" by blast
          from vor1 vor2 Greater3 have "y \<^bold>> x" by blast
          from this a have False by simp
        }
        ultimately have False by (rule exE)
      }
      ultimately have False by (rule exE)
      thus ?thesis by simp
    qed
    from 0 this have "God x \<and> re x" by (rule conjI)
    hence "\<exists>x. God x \<and> re x" by (rule exI)
  }
  from ExUnd this show ?thesis by (rule exE)
qed

(* Vereinfacht *)
theorem "God!3Ver":
  assumes P_re:
          P_re
  assumes Greater3:
          Greater3
  assumes Realization:
          Realization
  assumes ExUnd:
          ExUnd
  shows "\<exists> x. (God x \<and> re x)"
proof -
  {
    fix x
    assume 0: "God x"
    {
      assume cas: "\<not>(re x)"
      from Realization P_re have "\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> P f) \<and>  P re" by simp
      from Realization have 1: "\<forall> f. P f \<longrightarrow> (f x \<longrightarrow> P f)" by simp
      from Realization have "\<exists>y. \<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> P f)" by blast
      moreover {
        fix y
        assume "\<forall>f. P f \<longrightarrow> (f y \<longleftrightarrow> P f)"
        hence 4: "\<forall>f. P f \<longrightarrow> f y" by simp
        hence "P re \<longrightarrow> re y" by (rule allE)
        from this P_re have re:"re y" by (rule mp)
        from 4 0 have a:"\<not> (y \<^bold>> x)" by simp
        from 4 have vor1: "\<forall>f. P f \<longrightarrow> (f x \<longrightarrow> f y)" by blast
        from P_re re cas have "P re \<and> re y \<and> \<not>(re x)" by simp
        hence vor2: "\<exists>F. (P F \<and> F y \<and> \<not>(F x))" by blast
        from vor1 vor2 Greater3 have "y \<^bold>> x" by blast
        from this a have False by simp
      }
      ultimately have False by (rule exE)
    }
    hence "re x" by (rule ccontr)
    from 0 this have "God x \<and> re x" by (rule conjI)
    hence "\<exists>x. God x \<and> re x" by (rule exI)
  }
  from ExUnd this show ?thesis by (rule exE)
qed

theorem "GodCanDoItAll":
  assumes P_re
  assumes Greater3
  assumes Realization
  assumes ExUnd
  shows "\<forall>f. P f \<longrightarrow> (\<exists>x. God x \<and> f x)"
proof -
  (* TODO *)
oops


consts D :: "(u \<Rightarrow> bool) \<Rightarrow> bool"

axiomatization where
  dsubstP: "\<forall>f. D f \<longrightarrow> P f"

(* do not further consider quasi id, because we have a different proof *)
abbreviation quasi_id where
  "quasi_id \<equiv> \<lambda>x y. \<forall>f. P f \<and> \<not>D f \<longrightarrow> f x = f y"

abbreviation Realization_W where
  "Realization_W \<equiv> \<forall> FF. subsetP FF \<longrightarrow> (\<exists>x. \<forall>f. FF f \<longrightarrow> f x)"

end