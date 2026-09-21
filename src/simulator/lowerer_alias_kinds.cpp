// §26.3 (printed page 810) with §3.12.1 (printed 56): the per-name records
// and objects a package's or the compilation unit's variable carries beside
// its storage, given to the alias a module's import, a package's export or
// the unit's binding into a module makes (AliasVariableKinds), so that a
// reference through the alias reaches the one object, layout and tag the
// storage has. Moved out of lowerer_import.cpp, which lowers the imports
// themselves, once the layout joined the kinds and the file reached the
// gate's length.

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

// §7.4.2 with §7.4.4 (printed page 154): the index suffixes of the elements
// of the fixed-size array `info` describes, "[1]" for a one-dimensional
// array's second element and "[1][0]" for a two-dimensional array's, each
// dimension's addresses counted from its low bound in declaration order, the
// spelling CreateArrayElements and CreateMultiDimLeaves (lowerer_var.cpp) key
// the element variables by. A one-dimensional array's extent is the lo and
// size pair, a multidimensional array's the per-dimension vectors.
static void CollectElementSuffixes(const ArrayInfo& info, size_t dim,
                                   const std::string& prefix,
                                   std::vector<std::string>& out) {
  bool multi = !info.dim_sizes.empty();
  size_t dims = multi ? info.dim_sizes.size() : 1;
  if (dim == dims) {
    out.push_back(prefix);
    return;
  }
  uint32_t lo = multi ? info.dim_los[dim] : info.lo;
  uint32_t size = multi ? info.dim_sizes[dim] : info.size;
  for (uint32_t i = 0; i < size; ++i) {
    CollectElementSuffixes(info, dim + 1,
                           prefix + "[" + std::to_string(lo + i) + "]", out);
  }
}

// §26.3 (printed page 810) with §7.4.2 (printed 154) and §7.5 (printed
// 157-158): the fixed-size or dynamic array a package `int a[2]` or `int d[]`
// declares, given to the alias `key`: the ArrayInfo CreatePackageArray or
// CreatePackageDynArray (lowerer_package_data.cpp) registered under `qname`,
// which foreach, $size and every element select read the shape from, copied
// under the alias as the queue and the associative array are, and each
// element variable of a fixed-size array, "p1.a[1]", aliased under the
// alias's own spelling of it, "a[1]" under the instance prefix, the key
// FindVariable answers a module's element by. A dynamic array's elements are
// the QueueObject's, which AliasQueue already shares. The alias carried the
// carrier variable alone, so `a[1] = 7` after `import p1::*` wrote bit 1 of
// the 32-bit carrier and `a[1]` read it back as one bit, `foreach (a[i])` ran
// once per bit, `$size(a)` answered the carrier's width, and `d.size()` and
// `d[2]` after the package's own `p1::d = new[3]` answered 0. The shape is
// copied before the alias is registered: the registration inserts into the
// table the found shape lives in.
static void AliasArray(std::string_view key, std::string_view qname,
                       SimContext& ctx, Arena& arena) {
  const ArrayInfo* found = ctx.FindArrayInfo(qname);
  if (found == nullptr) return;
  ArrayInfo info = *found;
  ctx.RegisterArray(key, info);
  if (info.is_dynamic) return;
  std::vector<std::string> suffixes;
  CollectElementSuffixes(info, 0, "", suffixes);
  for (const std::string& suffix : suffixes) {
    auto* elem_key = arena.Create<std::string>(std::string(key) + suffix);
    ctx.AliasVariable(*elem_key, std::string(qname) + suffix);
  }
}

// §7.2.1 (printed page 147) with §11.9 (printed 304) and §26.3 (printed
// 810): the structure or union layout the storage under `qname` was bound
// to -- RegisterPackageDataLayout (lowerer_package_data.cpp) binds a
// package's or the unit's variable to its typedef's registration or to one
// built for an inline type -- given to the alias `key`, so that `u.b` in a
// module declaring no u, bound to the unit's "$unit.u" by AliasUnitDataItems,
// reads b through the unit variable's layout (StructLayoutOfName in
// eval_member_path.cpp); the alias carried the storage alone, so the read
// resolved through no layout and answered 0. §11.9 keeps one tag per tagged
// union variable, and the tag table (SimContext::var_tags_) is keyed by
// name with no alias of its own, so the one key every spelling records and
// reads the tag under is the key the layout is registered by where that key
// names the variable's own storage (TagKeyOfName): a module's declaration
// registers its layout under its storage key (RegisterAggregateLayout), and
// a storage bound to its typedef's registration, which names no variable,
// is given a registration of its own under its key here, the copy's
// type_name spelling that key as the builder spells a registration's, before
// the alias is bound to it. Bound to the typedef's key, a retag through the
// alias, `u = tagged Other 3;` in the module, stood under the alias's name
// while `$unit::u.Valid` read the initializer's Valid under "$unit.u",
// passing a read §11.9 reports.
static void AliasLayout(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena) {
  const StructTypeInfo* found = ctx.GetVariableStructType(qname);
  if (found == nullptr) return;
  std::string_view stored = found->type_name;
  if (stored != qname) {
    StructTypeInfo own = *found;
    stored = *arena.Create<std::string>(std::string(qname));
    own.type_name = stored;
    ctx.RegisterStructType(stored, own);
    ctx.SetVariableStructType(stored, stored);
  }
  ctx.SetVariableStructType(key, stored);
}

// The per-name records a package variable is entered in beside its storage,
// keyed "pkg.name" as the storage is, given to the alias `key` from the
// declaring package's `qname`: the class the variable is declared with
// (RegisterPackageClassVariables in lowerer_package_class_vars.cpp), which
// TryClassNewAssign (statement_assign_object.cpp) asks for under the target's
// own key before it constructs, so that `p2::h = new` through the exporter
// and `h = new` after a module's `import p1::h` each found no class, built
// nothing and left the handle null; and the real registration
// ShapePackageVariable (lowerer_register.cpp) makes; and the queue or the
// associative array a package `int q[$]` or `int m[string]` declares
// (CreatePackageAggregate in lowerer_package_data.cpp), which FindQueue and
// FindAssocArray answer by their own keys, so that `q.push_back(4)` after
// `import p1::q` and `p2::q.size()` through an exporter reached no object;
// and the fixed-size or dynamic array's shape and elements (AliasArray);
// and the structure or union layout (AliasLayout), through which a tagged
// union's tag is reached. A string's kind is a flag of the Variable itself,
// which the alias already shares. Shared with AliasUnitDataItems
// (lowerer_package_data.cpp), which binds the unit's items into a module the
// same way.
void AliasVariableKinds(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena) {
  std::string_view cls = ctx.GetVariableClassType(qname);
  if (!cls.empty()) ctx.SetVariableClassType(key, cls);
  if (ctx.IsRealVariable(qname)) ctx.RegisterRealVariable(key);
  // §6.19.5 with §26.3: the enumeration a package's variable or parameter is
  // declared with (RegisterPackageDataEnumType in lowerer_package_data.cpp),
  // so `pc.num()` and `EC.name()` after `import p1::*` walk its members.
  if (const EnumTypeInfo* info = ctx.GetVariableEnumType(qname))
    ctx.SetVariableEnumType(key, info->type_name);
  ctx.AliasQueue(key, qname);
  ctx.AliasAssocArray(key, qname);
  AliasArray(key, qname, ctx, arena);
  AliasLayout(key, qname, ctx, arena);
  // §15.3 and §15.4: a package's semaphore or mailbox the same way, so `s.get`
  // after `import p1::s` and `p2::s` through an export reach the one bucket.
  ctx.AliasSemaphore(key, qname);
  ctx.AliasMailbox(key, qname);
}

}  // namespace delta
