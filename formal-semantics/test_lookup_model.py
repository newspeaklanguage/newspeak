import unittest

from lookup_model import (
    Access,
    Class,
    Method,
    lookup_protected,
    lookup_public,
    lookup_unrestricted,
    ordinary_dispatch,
    outer_dispatch,
    super_dispatch,
)


def method(selector, access, owner):
    return Method(selector, access, owner)


class LookupSemanticsTests(unittest.TestCase):
    def setUp(self):
        dnu = method("doesNotUnderstand:", Access.PROTECTED, "ObjectDecl")
        public_m = method("m", Access.PUBLIC, "ObjectDecl")
        self.object = Class(
            "Object", "ObjectDecl", methods={"doesNotUnderstand:": dnu, "m": public_m}
        )

    def test_public_lookup_finds_public_method(self):
        child = Class("Child", "ChildDecl", self.object)
        found, owner = lookup_public("m", child)
        self.assertEqual(found.access, Access.PUBLIC)
        self.assertIs(owner, self.object)

    def test_protected_override_is_barrier_to_ordinary_send(self):
        protected_m = method("m", Access.PROTECTED, "ChildDecl")
        child = Class("Child", "ChildDecl", self.object, {"m": protected_m})
        self.assertIsNone(lookup_public("m", child))
        kind, selected, _ = ordinary_dispatch("m", child)
        self.assertEqual(kind, "dnu")
        self.assertEqual(selected.selector, "doesNotUnderstand:")

    def test_private_declaration_is_transparent_to_public_lookup(self):
        private_m = method("m", Access.PRIVATE, "ChildDecl")
        child = Class("Child", "ChildDecl", self.object, {"m": private_m})
        found, owner = lookup_public("m", child)
        self.assertEqual(found.access, Access.PUBLIC)
        self.assertIs(owner, self.object)

    def test_protected_lookup_sees_protected_method(self):
        protected_m = method("m", Access.PROTECTED, "ChildDecl")
        child = Class("Child", "ChildDecl", self.object, {"m": protected_m})
        found, owner = lookup_protected("m", child)
        self.assertIs(found, protected_m)
        self.assertIs(owner, child)

    def test_unrestricted_lookup_sees_private_method(self):
        private_m = method("m", Access.PRIVATE, "ChildDecl")
        child = Class("Child", "ChildDecl", self.object, {"m": private_m})
        found, owner = lookup_unrestricted("m", child)
        self.assertIs(found, private_m)
        self.assertIs(owner, child)

    def test_private_outer_send_is_lexically_bound(self):
        private_m = method("m", Access.PRIVATE, "OuterDecl")
        outer_application = Class(
            "Outer@o", "OuterDecl", self.object, {"m": private_m}
        )
        overriding_m = method("m", Access.PUBLIC, "DerivedOuterDecl")
        derived = Class(
            "DerivedOuter", "DerivedOuterDecl", outer_application, {"m": overriding_m}
        )
        kind, selected, current_class = outer_dispatch("m", derived, "OuterDecl")
        self.assertEqual(kind, "invoke-private")
        self.assertIs(selected, private_m)
        self.assertIs(current_class, outer_application)

    def test_nonprivate_outer_send_remains_virtual(self):
        protected_m = method("m", Access.PROTECTED, "OuterDecl")
        outer_application = Class(
            "Outer@o", "OuterDecl", self.object, {"m": protected_m}
        )
        overriding_m = method("m", Access.PUBLIC, "DerivedOuterDecl")
        derived = Class(
            "DerivedOuter", "DerivedOuterDecl", outer_application, {"m": overriding_m}
        )
        kind, selected, current_class = outer_dispatch("m", derived, "OuterDecl")
        self.assertEqual(kind, "invoke")
        self.assertIs(selected, overriding_m)
        self.assertIs(current_class, derived)

    def test_super_lookup_starts_above_current_class(self):
        base_m = method("m", Access.PROTECTED, "BaseDecl")
        base = Class("Base", "BaseDecl", self.object, {"m": base_m})
        child_m = method("m", Access.PUBLIC, "ChildDecl")
        child = Class("Child", "ChildDecl", base, {"m": child_m})
        kind, selected, current_class = super_dispatch("m", child)
        self.assertEqual(kind, "invoke")
        self.assertIs(selected, base_m)
        self.assertIs(current_class, base)

    def test_super_dnu_lookup_also_starts_above_current_class(self):
        private_dnu = method("doesNotUnderstand:", Access.PRIVATE, "ChildDecl")
        child = Class(
            "Child", "ChildDecl", self.object, {"doesNotUnderstand:": private_dnu}
        )
        kind, selected, current_class = super_dispatch("absent", child)
        self.assertEqual(kind, "dnu")
        self.assertIs(selected, self.object.methods["doesNotUnderstand:"])
        self.assertIs(current_class, self.object)


if __name__ == "__main__":
    unittest.main()
