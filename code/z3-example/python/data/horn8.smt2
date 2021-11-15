(declare-rel Invariant Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool))
(declare-rel Goal ())
(declare-var A Bool)
(declare-var B Bool)
(declare-var C Bool)
(declare-var D Bool)
(declare-var E Bool)
(declare-var F Bool)
(declare-var G Bool)
(declare-var H Bool)
(declare-var I Bool)
(declare-var J Bool)
(declare-var K Bool)
(declare-var L Bool)
(declare-var M Bool)
(declare-var N Bool)
(declare-var O Bool)
(declare-var P Bool)
(declare-var Q Bool)
(declare-var R Bool)
(declare-var S Bool)
(declare-var T Bool)
(declare-var U Bool)
(declare-var V Bool)
(declare-var W Bool)
(declare-var X Bool)
(declare-var Y Bool)
(declare-var Z Bool)
(declare-var A1 Bool)
(rule (let ((a!1 (and (not B)
                (not F)
                J
                (not K)
                A1
                (not (and D (not E)))
                (or (not F) (= G A)))))
  (=> a!1 (Inv A B C D E F G H I J K))))
(rule (let ((a!1 (ite Y H (ite E (bvadd #x1 (bvmul #x2 H)) A)))
      (a!2 (= T (ite Y I (bvadd #x1 (bvmul #x2 H))))))
(let ((a!3 (and (Inv A B C D E F G H I J K)
                (= L (ite Y A (ite D I A)))
                (= M (and (not Y) F))
                (= N (bvadd #x1 (bvmul #x2 G)))
                (= O (ite Y D E))
                (= P (ite Y E A1))
                (= Q (and (not Y) K))
                (= R (ite Y X G))
                (= S a!1)
                a!2
                (= U Y)
                (= V (and (not Y) J))
                A1
                (not (and D (not E)))
                (or (not F) (= G A)))))
  (=> a!3 (Inv L M N O P Q R S T U V)))))
(rule (let ((a!1 (and (Inv Z A1 X Y W V T S R U Q)
                (not (or (not A1) (= X Z)))
                B
                (not (and Y (not W)))
                (or (not V) (= T Z)))))
  (=> a!1 Goal)))
(query Goal)