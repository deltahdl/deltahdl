#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr int kMemberRelations[] = {
    vpiVariables,       vpiMethods, vpiConstraint,   vpiNamedEvent,
    vpiNamedEventArray, vpiTypedef, vpiInternalScope};

class SpecializationsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle DefnOf(const char* scope, std::string_view name) {
    return Named(vpiClassDefn, scope == nullptr ? nullptr : By(scope), name);
  }

  static vpiHandle TypespecOf(vpiHandle obj) {
    return obj == nullptr ? nullptr : vpi_handle(vpiClassTypespec, obj);
  }

  static vpiHandle ObjTypespecOf(const char* var) {
    return TypespecOf(vpi_handle(vpiClassObj, By(var)));
  }

  static vpiHandle ExtendsTypespecOf(vpiHandle defn) {
    return defn == nullptr ? nullptr : TypespecOf(vpi_handle(vpiExtends, defn));
  }

  static vpiHandle Unit() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }

  static int ParamValue(vpiHandle typespec, std::string_view name) {
    vpiHandle param =
        typespec == nullptr ? nullptr : Named(vpiParameter, typespec, name);
    return param == nullptr ? -1 : IntegerOf(param);
  }

  static vpiHandle AssignedRhs(vpiHandle typespec, std::string_view name) {
    if (typespec == nullptr) return nullptr;
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      vpiHandle lhs = vpi_handle(vpiLhs, assign);
      const char* own = lhs == nullptr ? nullptr : vpi_get_str(vpiName, lhs);
      if (own != nullptr && name == own) return vpi_handle(vpiRhs, assign);
    }
    return nullptr;
  }

  static int AssignedValue(vpiHandle typespec, std::string_view name) {
    vpiHandle rhs = AssignedRhs(typespec, name);
    return rhs == nullptr ? -1 : IntegerOf(rhs);
  }

  static std::vector<int> RelationsAnswered(vpiHandle typespec) {
    std::vector<int> answered;
    for (const int kRelation : kMemberRelations) {
      if (!ObjectsOf(kRelation, typespec).empty())
        answered.push_back(kRelation);
    }
    return answered;
  }

  static bool Lists(const std::vector<std::string>& names,
                    std::string_view name) {
    return std::ranges::find(names, name) != names.end();
  }

  static std::vector<std::string> DeclaredOrder(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      const char* name = vpi_get_str(vpiName, obj);
      names.emplace_back(name == nullptr ? "" : name);
    }
    return names;
  }

  static std::vector<vpiHandle> DefnsOf(const std::vector<vpiHandle>& specs) {
    std::vector<vpiHandle> defns;
    defns.reserve(specs.size());
    for (vpiHandle spec : specs) {
      defns.push_back(vpi_handle(vpiClassDefn, spec));
    }
    return defns;
  }
};

constexpr const char* kLexicalForms =
    "module top;\n"
    "  localparam int K = 4;\n"
    "  class B #(int W = 1);\n"
    "    int x;\n"
    "    event e;\n"
    "    event ea[2];\n"
    "    typedef int t_t;\n"
    "    constraint c { x > 0; }\n"
    "    task t; endtask\n"
    "    class N; endclass\n"
    "  endclass\n"
    "  class D extends B #(2); endclass\n"
    "  class S extends B #(K + 1); endclass\n"
    "  class H;\n"
    "    B #(3) p;\n"
    "    B pd;\n"
    "    typedef B #(4) b_t;\n"
    "    function B #(5) f(); return null; endfunction\n"
    "    task g(B #(6) a); endtask\n"
    "  endclass\n"
    "  D d = new;\n"
    "  H h = new;\n"
    "endmodule\n";

class LexicalTypespecs : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kLexicalForms);
  }

  static vpiHandle H() { return DefnOf("top", "H"); }

  static vpiHandle MethodOfH(std::string_view name) {
    return Named(vpiMethods, H(), name);
  }

  static void ExpectLexicalOfB(vpiHandle typespec, int written) {
    ASSERT_NE(typespec, nullptr);
    EXPECT_EQ(vpi_get(vpiType, typespec), vpiClassTypespec);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
              VpiObjectOf(DefnOf("top", "B")));
    EXPECT_EQ(AssignedValue(typespec, "W"), written);
    EXPECT_EQ(RelationsAnswered(typespec), std::vector<int>{});
  }
};

TEST_F(LexicalTypespecs, AnExtendsClausesTypespecAnswersNoMemberRelation) {
  ExpectLexicalOfB(ExtendsTypespecOf(DefnOf("top", "D")), 2);
}

TEST_F(LexicalTypespecs, AClassItemsTypespecAnswersNoMemberRelation) {
  const vpiHandle kSpecs[] = {TypespecOf(Named(vpiVariables, H(), "p")),
                              TypespecOf(Named(vpiVariables, H(), "pd")),
                              Named(vpiTypedef, H(), "b_t")};
  for (vpiHandle spec : kSpecs) {
    ASSERT_NE(spec, nullptr);
    EXPECT_EQ(vpi_get(vpiType, spec), vpiClassTypespec);
    EXPECT_EQ(RelationsAnswered(spec), std::vector<int>{});
  }
}

TEST_F(LexicalTypespecs, DISABLED_APropertysTypespecIsLexical) {
  ExpectLexicalOfB(TypespecOf(Named(vpiVariables, H(), "p")), 3);
}

TEST_F(LexicalTypespecs,
       DISABLED_ADefaultedPropertysTypespecAssignsTheDefault) {
  ExpectLexicalOfB(TypespecOf(Named(vpiVariables, H(), "pd")), 1);
}

TEST_F(LexicalTypespecs, DISABLED_AClassBodyTypedefIsALexicalTypespec) {
  vpiHandle typedef_spec = Named(vpiTypedef, H(), "b_t");
  ExpectLexicalOfB(typedef_spec, 4);
  EXPECT_STREQ(vpi_get_str(vpiName, typedef_spec), "b_t");
}

TEST_F(LexicalTypespecs, DISABLED_AMethodsReturnTypespecIsLexical) {
  ExpectLexicalOfB(TypespecOf(vpi_handle(vpiReturn, MethodOfH("f"))), 5);
}

TEST_F(LexicalTypespecs, DISABLED_AMethodsFormalTypespecIsLexical) {
  vpiHandle formal = Named(vpiIODecl, MethodOfH("g"), "a");
  ASSERT_NE(formal, nullptr);
  ExpectLexicalOfB(TypespecOf(vpi_handle(vpiExpr, formal)), 6);
}

TEST_F(LexicalTypespecs, AnExtendsClausesExpressionIsAssignedAsWritten) {
  vpiHandle rhs = AssignedRhs(ExtendsTypespecOf(DefnOf("top", "S")), "W");
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(vpi_get(vpiType, rhs), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, rhs), vpiAddOp);
  std::vector<vpiHandle> operands = OperandsOf(rhs);
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, operands[0]), "K");
  EXPECT_EQ(vpi_get(vpiType, operands[1]), vpiConstant);
  EXPECT_EQ(IntegerOf(operands[1]), 1);
}

TEST_F(LexicalTypespecs, ALexicalTypespecIsOfAUserDefinedClass) {
  EXPECT_EQ(vpi_get(vpiClassType, ExtendsTypespecOf(DefnOf("top", "D"))),
            vpiUserDefinedClass);
  EXPECT_EQ(vpi_get(vpiClassType, TypespecOf(Named(vpiVariables, H(), "p"))),
            vpiUserDefinedClass);
}

TEST_F(LexicalTypespecs, DISABLED_ALexicalTypespecYieldsItsClasssParameters) {
  vpiHandle typespec = ExtendsTypespecOf(DefnOf("top", "D"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(NamesOf(vpiParameter, typespec), std::vector<std::string>{"W"});
  EXPECT_EQ(vpi_get(vpiLocalParam, Named(vpiParameter, typespec, "W")), 0);
}

constexpr const char* kMembersOfASpecialization =
    "module top;\n"
    "  class S #(int W = 1);\n"
    "    int a;\n"
    "    static int s;\n"
    "    event e;\n"
    "    static event se;\n"
    "    event ea[2];\n"
    "    static event sea[2];\n"
    "    task t; endtask\n"
    "    function int f(); return 1; endfunction\n"
    "    static function int sf(); return 2; endfunction\n"
    "    function new(); endfunction\n"
    "    function void pre_randomize(); endfunction\n"
    "    function void post_randomize(); endfunction\n"
    "    class N; endclass\n"
    "  endclass\n"
    "  class Q #(int W = 1); endclass\n"
    "  class X;\n"
    "    rand int a;\n"
    "    constraint z { a > 0; }\n"
    "    extern constraint m;\n"
    "    constraint b { a < 9; }\n"
    "  endclass\n"
    "  constraint X::m { a != 3; }\n"
    "  S #(2) v = new;\n"
    "  Q q1 = new;\n"
    "  Q #() q2 = new;\n"
    "  X xv = new;\n"
    "endmodule\n";

class MembersOfASpecialization : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kMembersOfASpecialization);
  }

  static vpiHandle V() { return TypespecOf(By("top.v")); }
};

TEST_F(MembersOfASpecialization, ItsVariablesAndEventsHaveEitherLifetime) {
  ASSERT_NE(V(), nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, V()), (std::vector<std::string>{"a", "s"}));
  EXPECT_EQ(NamesOf(vpiNamedEvent, V()), (std::vector<std::string>{"e", "se"}));
}

TEST_F(MembersOfASpecialization, ItsEventArraysHaveEitherLifetime) {
  ASSERT_NE(V(), nullptr);
  EXPECT_EQ(NamesOf(vpiNamedEventArray, V()),
            (std::vector<std::string>{"ea", "sea"}));
}

TEST_F(MembersOfASpecialization,
       ItsMethodsAreTasksAndFunctionsOfEitherLifetime) {
  const std::vector<std::string> kMethods = NamesOf(vpiMethods, V());
  EXPECT_TRUE(Lists(kMethods, "t"));
  EXPECT_TRUE(Lists(kMethods, "f"));
  EXPECT_TRUE(Lists(kMethods, "sf"));
  EXPECT_FALSE(Lists(kMethods, "randomize"));
  EXPECT_FALSE(Lists(kMethods, "srandom"));
}

TEST_F(MembersOfASpecialization, AMethodDeclaredWithABuiltInNameIsAMethod) {
  const std::vector<std::string> kMethods = NamesOf(vpiMethods, V());
  EXPECT_TRUE(Lists(kMethods, "new"));
  EXPECT_TRUE(Lists(kMethods, "pre_randomize"));
  EXPECT_TRUE(Lists(kMethods, "post_randomize"));
}

TEST_F(MembersOfASpecialization, ANestedClassIsAnInternalScope) {
  vpiHandle nested = Named(vpiInternalScope, V(), "N");
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nested), vpiClassDefn);
}

TEST_F(MembersOfASpecialization, EverySpecializationHasANonEmptyName) {
  std::vector<vpiHandle> named = {V(), ObjTypespecOf("top.v"),
                                  TypespecOf(By("top.q1")),
                                  TypespecOf(By("top.q2"))};
  for (vpiHandle spec : ObjectsOf(vpiClassTypespec, DefnOf("top", "S"))) {
    named.push_back(spec);
  }
  ASSERT_GE(named.size(), 5u);
  for (vpiHandle spec : named) {
    ASSERT_NE(spec, nullptr);
    const char* name = vpi_get_str(vpiName, spec);
    ASSERT_NE(name, nullptr);
    EXPECT_NE(std::string(name), "");
  }
}

TEST_F(MembersOfASpecialization,
       ASpecializationIsAutomaticEveryWayItIsReached) {
  std::vector<vpiHandle> reached =
      ObjectsOf(vpiClassTypespec, DefnOf("top", "S"));
  ASSERT_FALSE(reached.empty());
  reached.push_back(V());
  reached.push_back(ObjTypespecOf("top.v"));
  for (vpiHandle spec : reached) {
    ASSERT_NE(spec, nullptr);
    EXPECT_EQ(vpi_get(vpiAutomatic, spec), 1);
  }
}

TEST_F(MembersOfASpecialization, ItsConstraintsComeInDeclarationOrder) {
  EXPECT_EQ(DeclaredOrder(vpiConstraint, TypespecOf(By("top.xv"))),
            (std::vector<std::string>{"z", "m", "b"}));
}

constexpr const char* kParametersOfASpecialization =
    "module top;\n"
    "  class C #(int W = 4, localparam int K = 1,\n"
    "            parameter type T = int);\n"
    "    parameter int P = 1;\n"
    "    localparam int L = 2;\n"
    "    parameter type PT = int;\n"
    "    localparam type LT = bit;\n"
    "  endclass\n"
    "  C #(.W(5), .T(byte)) c = new;\n"
    "  C cd = new;\n"
    "endmodule\n";

class ParametersOfASpecialization : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kParametersOfASpecialization);
  }

  static int LocalOf(std::string_view name) {
    return vpi_get(vpiLocalParam,
                   Named(vpiParameter, TypespecOf(By("top.c")), name));
  }

  static int KindOf(std::string_view name) {
    return vpi_get(vpiType, Named(vpiParameter, TypespecOf(By("top.c")), name));
  }
};

TEST_F(ParametersOfASpecialization, ItsBodyValueParametersAreLocal) {
  const std::vector<std::string> kNames =
      NamesOf(vpiParameter, TypespecOf(By("top.c")));
  for (const char* name : {"W", "K", "T", "P", "L"}) {
    EXPECT_TRUE(Lists(kNames, name)) << name;
  }
  EXPECT_EQ(LocalOf("P"), 1);
  EXPECT_EQ(LocalOf("L"), 1);
  EXPECT_EQ(KindOf("P"), vpiParameter);
}

TEST_F(ParametersOfASpecialization, DISABLED_ItsBodyTypeParametersAreLocal) {
  const std::vector<std::string> kNames =
      NamesOf(vpiParameter, TypespecOf(By("top.c")));
  for (const char* body : {"PT", "LT"}) {
    EXPECT_TRUE(Lists(kNames, body)) << body;
    EXPECT_EQ(LocalOf(body), 1) << body;
    EXPECT_EQ(KindOf(body), vpiTypeParameter) << body;
  }
}

TEST_F(ParametersOfASpecialization, APortValueParameterIsLocalWhenDeclaredSo) {
  EXPECT_EQ(LocalOf("W"), 0);
  EXPECT_EQ(LocalOf("K"), 1);
  EXPECT_EQ(KindOf("W"), vpiParameter);
}

TEST_F(ParametersOfASpecialization, APortTypeParameterIsATypeParameter) {
  EXPECT_EQ(KindOf("T"), vpiTypeParameter);
}

TEST_F(ParametersOfASpecialization, DISABLED_APortTypeParameterIsNotLocal) {
  EXPECT_EQ(LocalOf("T"), 0);
}

TEST_F(ParametersOfASpecialization, DISABLED_ATypeParametersRhsIsTheBoundType) {
  vpiHandle given = AssignedRhs(TypespecOf(By("top.c")), "T");
  vpiHandle defaulted = AssignedRhs(TypespecOf(By("top.cd")), "T");
  ASSERT_NE(given, nullptr);
  ASSERT_NE(defaulted, nullptr);
  EXPECT_EQ(vpi_get(vpiType, given), vpiByteTypespec);
  EXPECT_EQ(vpi_get(vpiType, defaulted), vpiIntTypespec);
}

constexpr const char* kTypespecMemberValues =
    "module top;\n"
    "  class C #(int W = 1);\n"
    "    int a = 5;\n"
    "    static int s = 3;\n"
    "    event e;\n"
    "    event ea[2];\n"
    "    static event se;\n"
    "  endclass\n"
    "  C #(2) h = new;\n"
    "  C #(2) k = new;\n"
    "endmodule\n";

class TypespecMemberValues : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kTypespecMemberValues);
  }

  static vpiHandle Member(int type, std::string_view name) {
    return Named(type, TypespecOf(By("top.h")), name);
  }

  static bool GetIsRefused(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -7;
    vpi_get_value(obj, &value);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    return kLevel == vpiError && value.value.integer == -7;
  }

  static bool PutIsRefused(vpiHandle obj, s_vpi_value* value) {
    vpiHandle returned = vpi_put_value(obj, value, nullptr, vpiNoDelay);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    return kLevel == vpiError && returned == nullptr;
  }

  static s_vpi_value IntValue(int integer) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = integer;
    return value;
  }
};

TEST_F(TypespecMemberValues, AnAutomaticPropertyRefusesTheValueRoutines) {
  vpiHandle a = Member(vpiVariables, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(GetIsRefused(a));
  s_vpi_value value = IntValue(9);
  EXPECT_TRUE(PutIsRefused(a, &value));
  EXPECT_EQ(
      IntegerOf(Named(vpiVariables, vpi_handle(vpiClassObj, By("top.h")), "a")),
      5);
}

TEST_F(TypespecMemberValues, AnAutomaticEventRefusesTheValueRoutines) {
  vpiHandle e = Member(vpiNamedEvent, "e");
  ASSERT_NE(e, nullptr);
  EXPECT_TRUE(GetIsRefused(e));
  EXPECT_TRUE(PutIsRefused(e, nullptr));
}

TEST_F(TypespecMemberValues,
       DISABLED_AnAutomaticEventArraysElementRefusesTheValueRoutines) {
  vpiHandle ea = Member(vpiNamedEventArray, "ea");
  ASSERT_NE(ea, nullptr);
  vpiHandle element = vpi_handle_by_index(ea, 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiNamedEvent);
  EXPECT_TRUE(GetIsRefused(element));
  EXPECT_TRUE(PutIsRefused(element, nullptr));
}

TEST_F(TypespecMemberValues, DISABLED_AStaticPropertyIsTheClasssOwnStorage) {
  vpiHandle s = Member(vpiVariables, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_FALSE(GetIsRefused(s));
  EXPECT_EQ(IntegerOf(s), 3);
  s_vpi_value value = IntValue(9);
  EXPECT_FALSE(PutIsRefused(s, &value));
  for (const char* var : {"top.h", "top.k"}) {
    EXPECT_EQ(
        IntegerOf(Named(vpiVariables, vpi_handle(vpiClassObj, By(var)), "s")),
        9)
        << var;
  }
}

TEST_F(TypespecMemberValues, DISABLED_AStaticEventAcceptsAPut) {
  vpiHandle se = Member(vpiNamedEvent, "se");
  ASSERT_NE(se, nullptr);
  EXPECT_FALSE(PutIsRefused(se, nullptr));
}

constexpr const char* kBuiltInClasses =
    "module top;\n"
    "  class M extends mailbox; endclass\n"
    "  semaphore sm = new;\n"
    "  M mm = new;\n"
    "  process p;\n"
    "  initial p = process::self();\n"
    "endmodule\n";

class BuiltInClassTypespecs : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kBuiltInClasses);
  }
};

TEST_F(BuiltInClassTypespecs, ASemaphoresTypespecHasNoClassDefn) {
  for (vpiHandle spec : {TypespecOf(By("top.sm")), ObjTypespecOf("top.sm")}) {
    ASSERT_NE(spec, nullptr);
    EXPECT_EQ(vpi_get(vpiClassType, spec), vpiSemaphoreClass);
    EXPECT_EQ(vpi_handle(vpiClassDefn, spec), nullptr);
  }
}

TEST_F(BuiltInClassTypespecs, AProcessVarsTypespecHasNoClassDefn) {
  vpiHandle spec = TypespecOf(By("top.p"));
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiClassType, spec), vpiProcessClass);
  EXPECT_EQ(vpi_handle(vpiClassDefn, spec), nullptr);
}

TEST_F(BuiltInClassTypespecs, DISABLED_AProcessObjsTypespecHasNoClassDefn) {
  vpiHandle spec = ObjTypespecOf("top.p");
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiClassType, spec), vpiProcessClass);
  EXPECT_EQ(vpi_handle(vpiClassDefn, spec), nullptr);
}

TEST_F(BuiltInClassTypespecs, ABuiltInBaseWrittenByAnExtendsHasNoClassDefn) {
  vpiHandle base = ExtendsTypespecOf(DefnOf("top", "M"));
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(vpi_get(vpiClassType, base), vpiMailboxClass);
  EXPECT_EQ(vpi_handle(vpiClassDefn, base), nullptr);
  EXPECT_EQ(vpi_get(vpiClassType, ObjTypespecOf("top.mm")),
            vpiUserDefinedClass);
}

constexpr const char* kUnparameterizedClasses =
    "package pk; class PA; int y; endclass endpackage\n"
    "class UA; int z; endclass\n"
    "module top;\n"
    "  class A; int x; endclass\n"
    "  class D extends A; endclass\n"
    "  A a = new;\n"
    "  D d = new;\n"
    "  pk::PA pa = new;\n"
    "  UA ua = new;\n"
    "endmodule\n";

class UnparameterizedClasses : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kUnparameterizedClasses);
  }
};

TEST_F(UnparameterizedClasses, ItsSpecializationReportsItsMembersEveryWay) {
  const std::vector<std::string> kX = {"x"};
  EXPECT_EQ(NamesOf(vpiVariables, TypespecOf(By("top.a"))), kX);
  EXPECT_EQ(NamesOf(vpiVariables, ObjTypespecOf("top.a")), kX);
  vpiHandle base = vpi_handle(vpiExtends, ObjTypespecOf("top.d"));
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, base), kX);
}

TEST_F(UnparameterizedClasses, ItsDefnYieldsExactlyItsOneSpecialization) {
  const struct {
    vpiHandle defn;
    const char* where;
  } kDefns[] = {{DefnOf("top", "A"), "top"},
                {DefnOf("pk", "PA"), "pk"},
                {Named(vpiClassDefn, Unit(), "UA"), "$unit"}};
  for (const auto& entry : kDefns) {
    ASSERT_NE(entry.defn, nullptr) << entry.where;
    std::vector<vpiHandle> specs = ObjectsOf(vpiClassTypespec, entry.defn);
    ASSERT_EQ(specs.size(), 1u) << entry.where;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, specs[0])),
              VpiObjectOf(entry.defn))
        << entry.where;
  }
}

constexpr const char* kSpecializationsInEveryPlace =
    "package pk;\n"
    "  class P #(int W = 1); int x; endclass\n"
    "  P #(2) pv = new;\n"
    "endpackage\n"
    "class U #(int W = 1); int x; endclass\n"
    "U #(3) uv = new;\n"
    "interface ifc;\n"
    "  class I #(int W = 1); int x; endclass\n"
    "  I #(4) iv = new;\n"
    "endinterface\n"
    "program prg;\n"
    "  class G #(int W = 1); int x; endclass\n"
    "  G #(5) gv = new;\n"
    "endprogram\n"
    "module top;\n"
    "  class C #(int W = 1); int x; endclass\n"
    "  typedef C #(6) c6_t;\n"
    "  c6_t tv = new;\n"
    "  ifc i();\n"
    "  prg r();\n"
    "  task tk; C #(7) lv; endtask\n"
    "  function void fn; C #(10) fv; endfunction\n"
    "  function C #(8) mk(); return null; endfunction\n"
    "  class K; function void m(); C #(9) mv; endfunction endclass\n"
    "endmodule\n";

class SpecializationsInEveryPlace : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kSpecializationsInEveryPlace);
  }

  static void ExpectSpecializationWith(vpiHandle var, int width,
                                       const std::string& where) {
    ASSERT_NE(var, nullptr) << where;
    vpiHandle spec = TypespecOf(var);
    ASSERT_NE(spec, nullptr) << where;
    EXPECT_EQ(ParamValue(spec, "W"), width) << where;
    EXPECT_EQ(NamesOf(vpiVariables, spec), std::vector<std::string>{"x"})
        << where;
  }
};

TEST_F(SpecializationsInEveryPlace, AnInterfacesClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(By("top.i.iv"), 4, "top.i");
}

TEST_F(SpecializationsInEveryPlace, AProgramsClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(By("top.r.gv"), 5, "top.r");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_APackagesClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(Named(vpiVariables, By("pk"), "pv"), 2, "pk");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_TheUnitsClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(Named(vpiVariables, Unit(), "uv"), 3, "$unit");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_ATasksClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(By("top.tk.lv"), 7, "top.tk");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_AFunctionsClassVarIsOfItsSpecialization) {
  ExpectSpecializationWith(By("top.fn.fv"), 10, "top.fn");
}

TEST_F(SpecializationsInEveryPlace, AVarOfATypedefIsOfTheSpecialization) {
  ExpectSpecializationWith(By("top.tv"), 6, "top.tv");
  vpiHandle spec = TypespecOf(By("top.tv"));
  ASSERT_NE(spec, nullptr);
  const char* name = vpi_get_str(vpiName, spec);
  ASSERT_NE(name, nullptr);
  EXPECT_NE(std::string(name), "c6_t");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_AModuleFunctionsReturnIsOfTheSpecialization) {
  vpiHandle mk = By("top.mk");
  ASSERT_NE(mk, nullptr);
  ExpectSpecializationWith(vpi_handle(vpiReturn, mk), 8, "top.mk");
}

TEST_F(SpecializationsInEveryPlace,
       DISABLED_AClassMethodsLocalIsNoSpecialization) {
  vpiHandle m = Named(vpiMethods, DefnOf("top", "K"), "m");
  ASSERT_NE(m, nullptr);
  vpiHandle spec = TypespecOf(Named(vpiVariables, m, "mv"));
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(AssignedValue(spec, "W"), 9);
  EXPECT_EQ(RelationsAnswered(spec), std::vector<int>{});
}

constexpr const char* kDerivedSpecializations =
    "module top;\n"
    "  class B #(int W = 1);\n"
    "    rand int x;\n"
    "    event e;\n"
    "    constraint c { x > 0; }\n"
    "    task t; endtask\n"
    "  endclass\n"
    "  class D extends B #(8);\n"
    "    constraint d1 { x < 9; }\n"
    "  endclass\n"
    "  class C extends B #(8); endclass\n"
    "  class D2 extends C; endclass\n"
    "  class R;\n"
    "    rand int a;\n"
    "    constraint c1 { a > 0; }\n"
    "    constraint c2 { a < 9; }\n"
    "  endclass\n"
    "  D d = new;\n"
    "  R rh = new;\n"
    "  initial void'(rh.randomize() with { a == 3; });\n"
    "endmodule\n";

class DerivedSpecializations : public SpecializationsOfARun {
 protected:
  void SetUp() override {
    SpecializationsOfARun::SetUp();
    Run(kDerivedSpecializations);
  }
};

TEST_F(DerivedSpecializations, ABaseDefnYieldsNoSpecializationOfADerivedClass) {
  vpiHandle b = DefnOf("top", "B");
  vpiHandle d = DefnOf("top", "D");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(d, nullptr);
  std::vector<vpiHandle> of_b = ObjectsOf(vpiClassTypespec, b);
  std::vector<vpiHandle> of_d = ObjectsOf(vpiClassTypespec, d);
  ASSERT_FALSE(of_b.empty());
  ASSERT_FALSE(of_d.empty());
  for (vpiHandle defn : DefnsOf(of_b)) {
    EXPECT_EQ(VpiObjectOf(defn), VpiObjectOf(b));
  }
  for (vpiHandle defn : DefnsOf(of_d)) {
    EXPECT_EQ(VpiObjectOf(defn), VpiObjectOf(d));
  }
}

TEST_F(DerivedSpecializations, TheBaseReachedThroughExtendsHasItsMembers) {
  vpiHandle base = vpi_handle(vpiExtends, ObjTypespecOf("top.d"));
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, base), std::vector<std::string>{"x"});
  EXPECT_EQ(NamesOf(vpiMethods, base), std::vector<std::string>{"t"});
  EXPECT_EQ(NamesOf(vpiConstraint, base), std::vector<std::string>{"c"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, base), std::vector<std::string>{"e"});
  EXPECT_EQ(NamesOf(vpiInternalScope, base), std::vector<std::string>{"t"});
}

TEST_F(DerivedSpecializations, ADerivedSpecializationLeavesOutBaseConstraints) {
  vpiHandle spec = ObjTypespecOf("top.d");
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(NamesOf(vpiConstraint, spec), std::vector<std::string>{"d1"});
  EXPECT_EQ(NamesOf(vpiConstraint, vpi_handle(vpiExtends, spec)),
            std::vector<std::string>{"c"});
}

TEST_F(DerivedSpecializations, DISABLED_ALexicalTypespecExtendsItsClasssBase) {
  vpiHandle c = ExtendsTypespecOf(DefnOf("top", "D2"));
  ASSERT_NE(c, nullptr);
  vpiHandle base = vpi_handle(vpiExtends, c);
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, base)),
            VpiObjectOf(DefnOf("top", "B")));
  EXPECT_EQ(AssignedValue(base, "W"), 8);
}

TEST_F(DerivedSpecializations, AnInlineConstraintIsNoConstraintOfATypespec) {
  std::vector<vpiHandle> specs =
      ObjectsOf(vpiClassTypespec, DefnOf("top", "R"));
  specs.push_back(TypespecOf(By("top.rh")));
  for (vpiHandle spec : specs) {
    ASSERT_NE(spec, nullptr);
    EXPECT_EQ(DeclaredOrder(vpiConstraint, spec),
              (std::vector<std::string>{"c1", "c2"}));
  }
}

TEST_F(SpecializationsOfARun, ATypeParameterBaseIsTheBoundClass) {
  Run("module top;\n"
      "  class B; int x; endclass\n"
      "  class B2; int y; endclass\n"
      "  class C2 #(type T = B) extends T; endclass\n"
      "  C2 #(B2) c = new;\n"
      "endmodule\n");
  vpiHandle base = vpi_handle(vpiExtends, ObjTypespecOf("top.c"));
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, base)),
            VpiObjectOf(DefnOf("top", "B2")));
}

}  // namespace
}  // namespace delta
