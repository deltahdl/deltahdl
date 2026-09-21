#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.19.2 (printed page 121, Table 6-10) with §26.6 (printed 815): `VAL[3]`
// generates the constants VAL0, VAL1 and VAL2, valued 0, 1 and 2, and a
// wildcard export hands the constants p1 declares on under p2's qualifier,
// so `p2::VAL2` and `p2::VAL1` are p1's: 2 * 10 + 1. The export walk held the
// member under its written name VAL, which no storage answers, so nothing
// was bound under "p2.VAL2" and both read 0. The reads stand in a declaration
// initializer: the elaborator's provided-name walk (AddEnumMemberNames in
// elaborator_scope_rules_names.cpp) holds the member under its written name
// too, so the same reads in a procedural statement are reported there as
// names p2 neither declares nor exports, a check that reaches no initializer.
TEST(PackageImportSim, WildcardReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §6.19.2 (printed page 121) with §26.6 (printed 815): an export naming one
// generated constant, `export p1::VAL2`, hands that constant on, so `p2::VAL2`
// and `p2::VAL1` after two such exports are p1's 2 and 1: 2 * 10 + 1. The
// walk matched a named export against the written names of the members
// alone, VAL2 among none of them, so neither key was bound and both read 0.
TEST(PackageImportSim, ExplicitlyReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::VAL2;\n"
                      "  export p1::VAL1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §6.19 (printed pages 119-120) with §7.2 (printed 146) and §26.6 (printed
// 815): an enumeration written as the type of a structure member declares
// its literals in the scope the structure is written in, so BUSY is a
// constant of p1 valued 1, and a wildcard export hands it on under p2's
// qualifier: 1 * 10 + 1 read through p2 and p1. The export walk read an
// item's top-level enumeration alone, so "p2.BUSY" was bound to nothing. The
// value depends on two registrations: the walk descending the member's
// inline type here, and RegisterPackageItemEnumConstants
// (lowerer_register.cpp) creating "p1.BUSY", without which both reads are 0.
TEST(PackageImportSim, ReExportedStructMemberLiteralThroughAWildcardExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef struct { enum {IDLE, BUSY} st; } s_t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::BUSY * 10 + p1::BUSY;\n"
                      "endmodule\n",
                      "y"),
            11u);
}

// §6.19 with §7.2 and §26.6 (printed 815): `export p1::BUSY` names the
// literal of a structure member's enumeration, a declaration of p1, so
// `p2::BUSY` is p1's 1: 1 * 10 + 1 read through p2 and p1. The walk matched a
// named export against the items' top-level enumerations alone, so the
// export bound nothing and the read through p2 was 0. Depends, as the
// wildcard form does, on RegisterPackageItemEnumConstants creating "p1.BUSY".
TEST(PackageImportSim, ReExportedStructMemberLiteralThroughAnExplicitExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef struct { enum {IDLE, BUSY} st; } s_t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::BUSY;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::BUSY * 10 + p1::BUSY;\n"
                      "endmodule\n",
                      "y"),
            11u);
}

// §26.3 (printed page 810) with §8.7 (printed 184): `import p1::h` makes
// p1's class-handle variable locally visible under its bare name, and `h =
// new` constructs an object of the class it is declared with into p1's h, so
// the property written through the bare name reads back through it and
// through p1's qualifier alike: 5 * 10 + 5. The import bound the bare name
// to the storage alone, with no class recorded under it, so the `new` had no
// class to construct, the handle stayed null and both reads answered 0.
TEST(PackageImportSim, ImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::h;\n"
                      "  import p1::C;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

// §26.3 (printed page 810) with §8.7: a wildcard import makes p1's h
// potentially locally visible, the reference binding it, and `h = new`
// constructs p1's C into it as the explicit import's does: 5 * 10 + 5 read
// through the bare name and p1's qualifier. The wildcard path binds the bare
// name through the same alias, which carried no class record, so the handle
// stayed null and both reads answered 0.
TEST(PackageImportSim,
     WildcardImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

// §7.10 (printed page 169) and §7.8 (printed 163) with §26.3 (printed 808):
// a package's `int q[$]` is a queue and its `int m[string]` an associative
// array, and a wildcard import makes each visible under its bare name, so
// two push_backs leave q[1] at 6 with a size of 2 and the write to m["k"]
// reads back 5: 6 * 100 + 2 * 10 + 5. The package's storage was the carrier
// variable alone, with no QueueObject or AssocArrayObject under "p1.q" or
// "p1.m", so the methods and the element selects found nothing and y was 0.
// The value depends on two bindings: CreatePackageDataVariables
// (lowerer_register.cpp) creating the objects under the package's keys, and
// the import's alias reaching them under the bare names.
TEST(PackageImportSim, WildcardImportedPackageQueueAndAssociativeArray) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  int m[string];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    q.push_back(4);\n"
                      "    q.push_back(6);\n"
                      "    m[\"k\"] = 5;\n"
                      "    y = q[1] * 100 + q.size() * 10 + m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            625u);
}

// §7.10 (printed page 169) and §7.8 with §26.3 (printed 808): `import p1::q`
// and `import p1::m` name the queue and the associative array explicitly,
// and each is p1's own object under its bare name; the queue is bounded
// `[$:1]`, so §7.10.5 discards the third push_back's element and it holds
// two, q[1] at 6: 6 * 100 + 2 * 10 + 5. An unbounded queue would keep the
// third and read 635. The explicit import binds the bare name through the
// same alias the wildcard one does, which reached the carrier variable
// alone.
TEST(PackageImportSim, ExplicitlyImportedPackageQueueAndAssociativeArray) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$:1];\n"
                      "  int m[string];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::q;\n"
                      "  import p1::m;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    q.push_back(4);\n"
                      "    q.push_back(6);\n"
                      "    q.push_back(8);\n"
                      "    m[\"k\"] = 5;\n"
                      "    y = q[1] * 100 + q.size() * 10 + m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            625u);
}

// §26.6 (printed pages 815-816) with §26.2 (printed 808): p3's `import p2::*`
// brings in the names p2 hands on through `export p1::*`, VAL2 and x among
// them, each the original declaration of p1, and a package's declaration
// assignment reads them as its subroutines would: 2 * 10 + 7. The
// initializers were evaluated before the exports were bound, so p3's search
// through p2 found no "p2.VAL2" and no "p2.x" and q was 0; the exports are
// now bound between the packages' storage and their initializers
// (RegisterDesignTypesAndPackages in lowerer.cpp).
TEST(PackageImportSim, PackageInitializerReadingWildcardReExportedNames) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::*;\n"
                      "  int q = VAL2 * 10 + x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::q;\n"
                      "endmodule\n",
                      "y"),
            27u);
}

// §26.6 (printed pages 815-816): the subclause's own p3 imports a name p2
// exports and reads it in a declaration assignment, `int q = x`, and an
// explicit `import p2::x` names p1's x through the export as the wildcard
// form does: 7. The explicit import's search reached the same unbound
// "p2.x" as the wildcard one's, so q read 0.
TEST(PackageImportSim, PackageInitializerReadingAnExplicitlyImportedReExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::x;\n"
                      "  int q = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::q;\n"
                      "endmodule\n",
                      "y"),
            7u);
}

// §15.3 (printed page 372) and §15.3.1 (printed 373) with §26.2 (printed
// 808): a package's `semaphore s = new(2)` is a bucket holding two keys
// before any procedure starts, so `p1::s.get(1)` procures one, the first
// try_get(1) the last, and the second try_get(1) finds the bucket empty and
// procures none: 1 * 10 + 0. The package's storage was a plain Variable, the
// initializer evaluated into it and no SemaphoreObject made under "p1.s", so
// the get() statement and both try_get() calls were served by no semaphore
// and y read 0. A discriminating shape: two get() calls and a try_get()
// would read 1 * 0 + 1 with and without the bucket alike.
TEST(PackageImportSim, PackageSemaphoreInitializedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore s = new(2);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::s.get(1);\n"
                      "    y = p1::s.try_get(1) * 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §15.3.1 (printed page 373) and §15.3.2 (printed 373) with §26.2 (printed
// 808): a package's `semaphore t` with no initializer is an empty bucket, as
// a module's is (CreateSyncObjectForVar in sync_variable.cpp), so
// `p1::t.put(3)` leaves three keys in it, `p1::t.get(1)` procures one, and
// three try_get(1) calls procure the two left and then none: 1 * 100 + 1 * 10 +
// 0. Under the same defect no bucket stood under "p1.t", the put() and the
// get() reached nothing and every try_get() answered 0.
TEST(PackageImportSim,
     PackageSemaphoreDeclaredWithoutInitializerThroughTheQualifier) {
  EXPECT_EQ(
      RunAndGet("package p1;\n"
                "  semaphore t;\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial begin\n"
                "    p1::t.put(3);\n"
                "    p1::t.get(1);\n"
                "    y = p1::t.try_get(1) * 100 + p1::t.try_get(1) * 10 +\n"
                "        p1::t.try_get(1);\n"
                "  end\n"
                "endmodule\n",
                "y"),
      110u);
}

// §7.4.2 (printed page 154) with §26.2 (printed 808) and §13.4: a package's
// `int a[4]` is an array of four elements, and the package's own functions
// read and write them by the bare name, so set(1, 7) and set(3, 2) land in
// two elements and get(1) and get(3) read them back: 7 * 10 + 2. The
// package's storage was the carrier variable alone, with no element
// variables and no ArrayInfo under "p1.a" (CreatePackageArray in
// lowerer_register.cpp), so each write went to one bit of the 32-bit carrier
// and each read answered that bit: 1 * 10 + 0.
TEST(PackageImportSim, PackageFixedSizeArrayReadAndWrittenInItsOwnFunctions) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "  function void set(int i, int v);\n"
                      "    a[i] = v;\n"
                      "  endfunction\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::set(1, 7);\n"
                      "    p1::set(3, 2);\n"
                      "    y = p1::get(1) * 10 + p1::get(3);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            72u);
}

// §12.7.3 with §7.4.2 (printed page 154) and §26.2 (printed 808): foreach
// over the package's own array inside its function runs once per element,
// and the elements hold what set() wrote, 7 and 2, the other two §6.8's 0
// for a 2-state int: 9. With no ArrayInfo under "p1.a" the loop ran once per
// bit of the carrier and each `a[i]` read one bit of it, the two writes
// having left the low bit of 7 at bit 1 and the low bit of 2 at bit 3: 1.
TEST(PackageImportSim, PackageFixedSizeArrayIteratedByForeachInItsOwnFunction) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "  function void set(int i, int v);\n"
                      "    a[i] = v;\n"
                      "  endfunction\n"
                      "  function int sum();\n"
                      "    int s = 0;\n"
                      "    foreach (a[i]) s += a[i];\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::set(1, 7);\n"
                      "    p1::set(3, 2);\n"
                      "    y = p1::sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            9u);
}

// §12.7.3 with §7.4.2 (printed page 154) and §26.3 (printed 808): foreach
// names the package's array through the package scope resolution operator,
// `p1::a`, which the loop reads the shape of under the "p1.a" key, so it
// runs four times. Under the same defect the name found no shape and the
// loop ran once per bit of the 32-bit carrier: 32.
TEST(PackageImportSim, PackageFixedSizeArrayCountedByForeachThroughQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = 0;\n"
                      "  initial foreach (p1::a[i]) y++;\n"
                      "endmodule\n",
                      "y"),
            4u);
}

// §7.5 and §7.5.1 (printed pages 157-158) with §26.3 (printed 808): a
// package's `int d[]` is a dynamic array, `p1::d = new[3]` sizes it to three
// elements, `p1::d[2] = 9` writes the last, and size() reads the three:
// 3 * 10 + 9. The package's storage was the carrier variable alone, with no
// QueueObject and no dynamic ArrayInfo under "p1.d" (CreatePackageDynArray
// in lowerer_register.cpp), so the new[] sized nothing, the write landed
// nowhere and both reads answered 0.
TEST(PackageImportSim, PackageDynamicArraySizedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int d[];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::d = new[3];\n"
                      "    p1::d[2] = 9;\n"
                      "    y = p1::d.size() * 10 + p1::d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            39u);
}

// §7.10 (printed page 169) with §26.2 (printed 808): a package queue's
// declaration assignment, `int q[$] = '{1, 2}`, supplies its two elements
// before any procedure starts, so size() reads 2 and q[1] reads 2:
// 2 * 10 + 2. The pattern was evaluated into the carrier variable rather
// than the QueueObject (InitPackageAggregate in lowerer_register.cpp), so
// the queue was empty and both reads answered 0.
TEST(PackageImportSim, PackageQueueInitializedByAnAssignmentPattern) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$] = '{1, 2};\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p1::q.size() * 10 + p1::q[1];\n"
                      "endmodule\n",
                      "y"),
            22u);
}

// §7.9.11 (printed page 169) with §7.8 (printed 163) and §26.2 (printed
// 808): a package associative array's literal gives it a default, so a read
// of an entry nothing wrote, `p1::m["x"]`, answers the default 7 rather
// than Table 7-1's 0. The literal lands in the AssocArrayObject under "p1.m"
// (InitPackageAggregate in lowerer_package_data.cpp), but the read through
// the qualifier resolved no array: ScopeResolvedAssocProperty
// (eval_array_class_assoc.cpp) took `p1::m` for a static property of a
// class p1 alone and never tried the "p1.m" key, so the select fell to a
// bit-select of the carrier and answered 0.
TEST(PackageImportSim, PackageAssociativeArrayInitializedWithADefault) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string] = '{default: 7};\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p1::m[\"x\"];\n"
                      "endmodule\n",
                      "y"),
            7u);
}

// §8.2 (printed page 179) with §7.10 (printed 169) and §26.2 (printed 808):
// a package queue of a class type holds handles, so `p1::q[1].v` names the
// property of the second object pushed and `p1::q[0].v` the first's:
// 4 * 10 + 3. The queue was created before the package's classes were
// lowered and left marked as holding plain values (holds_class_handles in
// CreatePackageAggregate, lowerer_register.cpp), so the element select
// followed by `.v` read no object's property and answered 0.
TEST(PackageImportSim, PackageQueueOfAClassTypeHoldsHandles) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
                      "    c1.v = 3;\n"
                      "    p1::q.push_back(c1);\n"
                      "    c2.v = 4;\n"
                      "    p1::q.push_back(c2);\n"
                      "    y = p1::q[1].v * 10 + p1::q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            43u);
}

// §7.4.2 (printed page 154) with §26.6 (printed 815-816) and §26.2 (printed
// 808): the subclause's own p3 imports what p2 exports of p1 and reads it in
// a declaration assignment, here the items of a fixed-size array's pattern,
// `int a[2] = '{VAL2, x}`, so a[0] is p1's VAL2, 2, and a[1] p1's x, 7,
// read by p3's own function: 2 * 10 + 7. The pattern was distributed over
// the elements when the array was created, ahead of the export binding
// (CreatePackageArray in lowerer_package_data.cpp), so neither item found
// "p2.VAL2" or "p2.x" and both elements read 0; the scalar `int q = x` was
// already read after the exports (InitPackageDataVariables).
TEST(PackageImportSim, PackageFixedSizeArrayInitializerReadingReExportedNames) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::*;\n"
                      "  int a[2] = '{VAL2, x};\n"
                      "  function int sum();\n"
                      "    return a[0] * 10 + a[1];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::sum();\n"
                      "endmodule\n",
                      "y"),
            27u);
}

// §15.5.2 (printed page 378) with §26.3 (printed 808): the event control's
// operand is a hierarchical_event_identifier, and a package's event is named
// through the package scope resolution operator, so `@(p1::e)` blocks the
// process until `-> p1::e` at time 3 triggers it: y reads 3. The control
// took an identifier alone for a named event (NamedEventKey in
// stmt_exec_wait.cpp), so the scoped operand went to the value-change
// awaiter, which resolved no variable for it and never resumed the process,
// and y stayed 0. The event's storage is marked as one by
// ShapePackageVariable (lowerer_package_data.cpp); left unmarked, the same
// trigger woke nothing either.
TEST(PackageImportSim, PackageEventAwaitedThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = 0;\n"
                      "  initial #3 -> p1::e;\n"
                      "  initial begin\n"
                      "    @(p1::e);\n"
                      "    y = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// §15.5.3 (printed page 378) with §26.3 (printed 808): the wait construct
// reads the triggered state of a hierarchical_event_identifier, a package's
// through its qualifier, so `wait (p1::e.triggered)` unblocks when `-> p1::e`
// fires at time 3: z reads 3. The wait armed on the names `p1` and `e` the
// read collection took the scoped operand apart into, neither the event's
// storage (CollectPackageScopedReads in stmt_exec_wait.cpp), so the process
// waited for ever and z stayed 0.
TEST(PackageImportSim, PackageEventTriggeredStateWaitedOnThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int z = 0;\n"
                      "  initial #3 -> p1::e;\n"
                      "  initial begin\n"
                      "    wait (p1::e.triggered);\n"
                      "    z = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "z"),
            3u);
}

// §15.5.3 (printed page 378) with §26.3 (printed 808): the triggered state
// persists through the time step, read as the bare member and as the
// method call alike, so both read 1 after `-> p1::e` in the same step:
// 1 * 10 + 1. With Variable::is_event clear on the package's storage
// (ShapePackageVariable in lowerer_package_data.cpp), the member read fell
// to a structure-member lookup and the call to the user-method lookup, and
// both answered 0.
TEST(PackageImportSim, PackageEventTriggeredStateReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    -> p1::e;\n"
                      "    y = p1::e.triggered * 10 + p1::e.triggered();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

// §8.3 (printed page 180) with §26.2 (printed 808): a package variable of a
// class type holds a handle, which LowerVar (lowerer_var.cpp) gives a
// module's at 64 bits whatever the declaration's own width, so the storage
// CreatePackageDataVariables makes under "p1.h" is 64 bits wide too
// (PackageDataWidth in lowerer_package_data.cpp). A class type is one no
// width table sizes, and such a type fell to the 32-bit carrier every
// unsized package item gets, so the handle's storage was half a handle.
TEST(PackageImportSim, PackageClassHandleCarrierIsSixtyFourBitsWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  class C;\n"
      "    int v;\n"
      "  endclass\n"
      "  C h;\n"
      "endpackage\n"
      "module top;\n"
      "  import p1::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* h = f.ctx.FindVariable("p1.h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->value.width, 64u);
}

// §8.3 (printed page 180) with §26.3 (printed 808): `p1::h = new` constructs
// an object of p1's C into the package's handle, which then compares unequal
// to null: 1. Read together with the width above so that a handle held in a
// 64-bit carrier still constructs and compares as it did in the narrower
// one.
TEST(PackageImportSim, PackageClassHandleConstructedThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = (p1::h != null);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

// §26.3 (printed page 808) with §13.4: a package function named through the
// scope resolution operator, `mypkg::add(1, 3)`, runs the package's
// function, and its formals `int a, b`, two names under one type, take the
// two actuals, 4. This is the shape of the suite's 26.3--package-ref.sv,
// which run 30725357212 reported failing (#2922) and every run since
// 35657769589 reports passing, with no case of the family pinning it.
TEST(PackageScopeReferenceSim,
     PackageFunctionWithFormalsUnderOneTypeCalledQualified) {
  EXPECT_EQ(RunAndGet("package mypkg;\n"
                      "  function int add(int a, b);\n"
                      "    return a + b;\n"
                      "  endfunction\n"
                      "endpackage : mypkg\n"
                      "module top();\n"
                      "  int y;\n"
                      "  initial y = mypkg::add(1, 3);\n"
                      "endmodule\n",
                      "y"),
            4u);
}

}  // namespace
