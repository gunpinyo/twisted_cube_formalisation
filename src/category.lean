universes u v

structure category :=
  (obj   : Type u)
  (hom   : obj → obj → Type v)
  (id    : Π (X : obj), hom X X)
  (comp  : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
  (id_l  : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f)
  (id_r  : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f)
  (assoc : ∀ {X Y Z W : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z W),
             comp (comp f g) h = comp f (comp g h))

namespace category
  structure iso (C : category) (X Y : C.obj) :=
    (f     : C.hom X Y)
    (g     : C.hom Y X)
    (fg_id : C.comp f g = C.id X)
    (gf_id : C.comp g f = C.id Y)
end category
