theory HartshorneCh1 imports Main begin

locale affine_plane_syntax =
  fixes Points :: "'a set" and Lines :: "'a set set"
begin

definition parallel (infix "||" 50)
  where "\<lbrakk> l \<in> Lines; m \<in> Lines \<rbrakk> \<Longrightarrow> l || m \<longleftrightarrow> l = m \<or> \<not> (\<exists> P \<in> Points. P \<in> l \<and> P \<in> m)"
end

definition collinear
  where "\<lbrakk>P \<in> Points; Q \<in> Points; R \<in> Points\<rbrakk> \<Longrightarrow> collinear P Q R \<longleftrightarrow> 
(\<exists>l. P \<in> l \<and> Q \<in> l \<and> R \<in> l)"

locale affine_plane = affine_plane_syntax +
  assumes 
a1: "\<lbrakk>P \<in> Points; Q \<in> Points; P \<noteq> Q \<rbrakk> \<Longrightarrow> \<exists>!l \<in> Lines. P \<in> l \<and> Q \<in> l" and
a2: "\<lbrakk>l \<in> Lines; P \<in> Points; P \<notin> l \<rbrakk> \<Longrightarrow> \<exists>!m \<in> Lines. l || m \<and> P \<in> m" and
a3: "\<exists> P Q R . (P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R) \<and> 
\<not> (\<exists>m \<in> Lines. P \<in> m \<and> Q \<in> m \<and> R\<in>m)"
begin

(* work on affine planes to take place here *)
(* perhaps define collinear? *)

(* try to prove, for instance, that if k and m are distinct, then they intersect in at 
most one point *)
(* NB: The axioms above are DELIBERATELY incorrect as stated. Let's try to fix them. *)

theorem collinear_comm: "\<lbrakk>A \<in> Points; B \<in> Points; C \<in> Points; collinear A B C\<rbrakk> \<Longrightarrow> collinear A C B"
  using collinear_def by fastforce

lemma parallel_symm[simp]: "\<lbrakk>l \<in> Lines; m \<in> Lines; l || m\<rbrakk> \<Longrightarrow> m || l"
  using parallel_def by blast

lemma parallel_refl[simp]: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> l || l"
  using parallel_def by blast

lemma parallel_trans[simp]: "\<lbrakk>l \<in> Lines; m \<in> Lines; n \<in> Lines; l || m; m || n\<rbrakk> \<Longrightarrow> l || n"
  by (metis a2 parallel_def)

(* Every point lies on some line *)
lemma line_for_point: "\<lbrakk>P \<in> Points\<rbrakk> \<Longrightarrow> \<exists>l \<in> Lines . P \<in> l"
  by (metis a1 a3)

lemma no_empty_line: "{} \<notin> Lines"
proof - 
  have "{} \<in> Lines \<Longrightarrow> False"
  proof-
    assume 1: "{} \<in> Lines"
    show False
      proof -
        obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> 
\<not> (\<exists>m \<in> Lines. P \<in> m \<and> Q \<in> m \<and> R\<in>m)" using a3 by blast
        obtain PQ where PQ: "PQ \<in> Lines \<and> P \<in> PQ \<and> Q \<in> PQ"
           using a1 PQR by metis
        obtain PR where PR: "PR \<in> Lines \<and> P \<in> PR \<and> R \<in> PR"
           using a1 PQR by metis
         have "PQ || {} \<and> PR || {}"
           by (simp add: "1" PQ PR parallel_def)
         moreover have "PQ \<noteq> PR" 
           using PQ PQR PR by blast
         ultimately have "(PQ \<in> Lines \<and> P \<in> PQ \<and> {} || PQ) \<and> (PR \<in> Lines \<and> P \<in> PR \<and> {} || PR)"
           by (simp add: \<open>PQ || {} \<and> PR || {}\<close> "1" PQ PR)
         thus False
           using "1" PQR \<open>PQ \<noteq> PR\<close> a2 by auto
      qed
    qed
    thus ?thesis by blast
qed

(* when saying P \<in> Points, try couldn't find the proof.
Why omit this statement? *)
(* Every line contains at least one point *)
lemma contained_point: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists>P . P \<in> l"
proof -
  assume l: "l \<in> Lines"
  have "l \<noteq> {}"
    using l no_empty_line by auto
  thus "\<exists> P .  P \<in> l" 
    by auto
qed

lemma four_point: "\<exists> P Q R S . P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and>
P \<noteq> Q \<and> P \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> R \<and> Q \<noteq> S"
proof -
  obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and>
    \<not> (\<exists>m \<in> Lines. P \<in> m \<and> Q \<in> m \<and> R \<in>m)" using a3 by blast
  obtain QR where QR: "QR \<in> Lines \<and> Q \<in> QR \<and> R \<in> QR" 
    using a1 PQR by metis
  obtain l where l: "l \<in> Lines \<and> l || QR \<and> P \<in> l"
    by (meson PQR QR affine_plane.a2 affine_plane_axioms parallel_symm)

  obtain PQ where PQ: "PQ \<in> Lines \<and> P \<in> PQ \<and> Q \<in> PQ" 
    using a1 PQR by metis
  obtain m where m : "m \<in> Lines \<and> m || PQ \<and> R \<in> m"
    by (meson PQR PQ affine_plane.a2 affine_plane_axioms parallel_symm)

  have "\<not>(l || m)"
    by (metis PQ PQR QR l m parallel_def parallel_trans)

  obtain S where S_meets : "S \<in> Points \<and> S \<in> l \<and>  S \<in> m"
    using \<open>\<not> l || m\<close> l m parallel_def by blast

  have "S \<notin> PQ" 
    using PQR PQ S_meets m parallel_def by blast   

  have "S \<notin> QR"
    using PQR QR S_meets l parallel_def by blast   

  have "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R" 
    using PQ QR \<open>S \<notin> PQ\<close> \<open>S \<notin> QR\<close> by blast

  thus ?thesis 
    using PQR by auto
qed

(* Every line contains at least two points *)
lemma contains_two_points: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P Q . P \<in> Points \<and> Q \<in> Points 
\<and> P \<in> l \<and> Q \<in> l \<and> P \<noteq> Q"
  sorry

lemma contains_three_points:  "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P Q R . (P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
\<and> P \<in> l \<and> Q \<in> l \<and> R \<in> l \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R)"
  nitpick

end (* affine_plane locale *)

end (* theory *)
