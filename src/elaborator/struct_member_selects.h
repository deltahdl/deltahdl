#pragma once

#include <cstddef>
#include <functional>

#include "elaborator/type_site_lookup.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct DataType;
struct Expr;

// A type written in a scope, the site it is written at, and the unpacked
// dimensions the typedefs it was reached through write after their names
// (§6.18, §7.4).
struct SitedType {
  const DataType* type = nullptr;
  TypeSite site = {};
  std::size_t dims = 0;
};

// §6.18 with §26.3: the type `named` stands for, through each typedef it is
// written as, each typedef's own type looked up as the scope declaring that
// typedef sees it before the typedef, and each typedef's unpacked dimensions
// added to those `named` counts. Each step reaches a declaration before the
// last in its scope, or a scope around it or a package, which leads to no
// module; a package reaches only one declared before it, a typedef naming no
// type the parser has not yet read, so the walk ends.
SitedType ThroughTypedefsAt(const CompilationUnit& unit, SitedType named);

// The type the variable a dotted name's first name `root` names is declared
// with, as written, at the site it is written at, with the unpacked
// dimensions written after the variable's name; no type where `root` names no
// variable whose type the scope tells.
using RootTypeOf = std::function<SitedType(const Expr& root)>;

// §23.7 a) with §7.2: a member access `access`, s.m, which is no scope
// resolution (§23.7.1), whose left-hand side reaches a structure or a union,
// from a variable `root_type` tells the type of, through selects of its
// unpacked elements (§7.4) and members of structure or union types, and that
// names none of the members that type declares. A path through a member of a
// class type reaches a property of the class (§8), not a structure. A random
// structure property of a class has rand_mode (§18.8), which it does not
// declare.
void ReportUndeclaredAggregateMember(const Expr& access,
                                     const CompilationUnit& unit,
                                     const RootTypeOf& root_type,
                                     DiagEngine& diag);

}  // namespace delta
