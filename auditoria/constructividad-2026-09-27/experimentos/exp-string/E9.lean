import FOL.Fresh0

/-! La trampa de instancias: que `ReflBEq`/`LawfulBEq String` elige la elaboracion por defecto
en un fichero que importa FOL (y por tanto Std.* del nucleo). -/
namespace ExpTrap
theorem t1 (a b : String) (h : (a == b) = false) : a ≠ b := not_eq_of_beq_eq_false h
theorem t2 (a b : String) : (a == b) = true ↔ a = b := beq_iff_eq
theorem t3 (a : String) : (a == a) = true := beq_self_eq_true a
theorem t4 (a b : String) (h : a = b) : (a == b) = true := beq_of_eq h
theorem t5 (a b : String) (h : (a == b) = true) : a = b := eq_of_beq h
end ExpTrap
set_option pp.explicit true in
#print ExpTrap.t1
#print axioms ExpTrap.t1
#print axioms ExpTrap.t2
#print axioms ExpTrap.t3
#print axioms ExpTrap.t4
#print axioms ExpTrap.t5
