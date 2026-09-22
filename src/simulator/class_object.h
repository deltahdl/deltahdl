#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

struct AssocArrayObject;
struct MailboxObject;
struct QueueObject;
struct SemaphoreObject;
struct ClassDecl;
struct ClassMember;
struct ConstraintForeachRef;
struct DataType;
struct Expr;
struct ModuleItem;
class Arena;

enum class Reachability : std::uint8_t {
  kStronglyReachable,
  kWeaklyReachable,
  kUnreachable,
};

struct ClassTypeInfo;
struct ClassTypespecInfo;

struct VTableEntry {
  std::string_view method_name;
  ModuleItem* method = nullptr;
  const ClassTypeInfo* owner = nullptr;
};

struct ClassTypeInfo {
  std::string_view name;
  const ClassTypeInfo* parent = nullptr;
  const ClassDecl* decl = nullptr;
  bool is_abstract = false;
  bool is_interface = false;
  // §37.32: a built-in class has no user-written declaration; its class-defn
  // relation reports NULL.
  bool is_builtin = false;
  std::vector<const ClassTypeInfo*> extended_interfaces;
  // §8.23: the class this one is declared inside, or nullptr for a class
  // declared at the scope of a compilation unit, package or module. A nested
  // class is registered under `Outer::Inner`, the name that reaches it from
  // outside, while a method of the containing class names it `Inner` and a
  // method of the nested class names the containing class's static properties
  // unqualified; both walk this chain (SimContext::FindClassType,
  // StaticPropertyOwner).
  const ClassTypeInfo* enclosing = nullptr;
  // §26.2: the package the class is declared in, "$unit" for a class the
  // compilation unit declares (§3.12.1, the unit's data keyed "$unit.name")
  // and empty for a module's. The scope's declarations are visible by their
  // bare names throughout it, the class's method bodies and property
  // initializers included, so a frame running one carries this name as
  // Scope::package and SimContext::FindInPackageScope answers them.
  std::string_view package;
  // §8.25 (printed page 204 of IEEE 1800-2023): the set of actual parameter
  // values this type is the generic class together with, as the `#(...)` list
  // naming the specialization wrote them, held in the arena so it outlives
  // the list it was copied from (SpecializationOf in
  // class_specialization.cpp). Null on the type registered for a class
  // declaration, which is §8.25.1's default specialization and takes the
  // declaration's own defaults. A name the specialization is reached by that
  // writes no list of its own -- a typedef of it, `typedef D#(integer) di;`
  // -- leaves the construction of `di u = new` nothing to bind the type
  // parameters from, and this is what it reads instead
  // (BindTypeParamActuals in eval_class_params.cpp).
  const std::vector<DataType>* param_actuals = nullptr;

  struct PropertyInfo {
    std::string_view name;
    uint32_t width = 32;
    bool is_static = false;
    bool is_local = false;
    bool is_protected = false;
    bool is_const = false;
    Expr* init_expr = nullptr;
    // §8.7: a property with no explicit default is initialized to its type's
    // uninitialized value during construction — X for a 4-state type, 0 for a
    // 2-state one. Recording the state-ness here lets the constructor pick the
    // right fill. Defaults to 2-state so entries that never set it (e.g. class
    // parameters) keep their prior zero-fill behavior.
    bool is_4state = false;
    // Whether `width` is the width the declaration gave the property, rather
    // than the 32-bit carrier substituted for a type the collector could not
    // size — a name, a string, a class handle. §8.7's fill needs a width for
    // either, which is why the carrier is stored; a write needs to know which
    // it has, because §10.7 truncating to a carrier would cut a handle in half
    // and a string down to four characters. `is_4state` is trustworthy on the
    // same condition and for the same reason: Is4stateType is asked with an
    // empty typedef map, so a name answers 2-state whatever it stands for.
    // Defaults to false so an entry that never set it is written unchanged.
    bool width_is_declared = false;
    // §6.12.1 converts a value crossing the real/integer boundary rather than
    // reinterpreting its bits, so a write to a real property has to convert
    // where a write to an integral one resizes. Recorded because the two are
    // told apart by the declared type and the stored Logic4Vec does not carry
    // it.
    bool is_real = false;
    // §6.16: whether the declaration wrote the string type, so that a string
    // method called on the property, `h.s.len()` or `s.len()` inside a
    // method, reads the text it holds (ReadStringReceiver in
    // src/simulator/eval_string.cpp). The stored Logic4Vec does not carry it:
    // a literal or a concatenation stored into the property is a packed value
    // (§5.9), and only the declaration says the property is a string.
    bool is_string = false;
    // §6.11.3: the signedness the declaration gives the property, which the
    // value stored in it carries. A variable keeps this on the Variable and a
    // read consults it there; a property is only its Logic4Vec, so the flag has
    // to be imposed on the value as it is written or a signed literal truncated
    // into an unsigned property reads back negative -- 240 into `bit [7:0]`
    // reading -16.
    bool is_signed = false;
    // §6.18/§7.2.1: the name of the type the declaration wrote, empty where it
    // wrote a type with no name of its own. It is what a member select of the
    // value the property holds resolves against: a property declared `pair_t p`
    // holds the whole structure in one value (§6.8), and the offset of `p.b`
    // within it is a fact about `pair_t` rather than about the property, which
    // SimContext::FindStructType answers by that name.
    std::string_view type_name = {};
    // §25.9: whether the declaration wrote `virtual interface`, so that the
    // value the property holds is the handle of the interface instance it
    // represents (SimContext::VirtualInterfaceHandle), 0 before it is
    // initialized, and a member reached through it by the dot notation is a
    // component of that instance. It is what makes `vif.clk` in a method of
    // the class -- read, written, or waited on -- the instance's own `clk`
    // rather than a member of a value that has none, as
    // Variable::is_virtual_interface does for a variable.
    bool is_virtual_interface = false;
    // §7.4.2: the element count of a property declared with one fixed unpacked
    // dimension, and the lowest index that dimension declares. The object
    // holds such a property's elements under the keys ClassArrayElementKey of
    // src/simulator/eval_class_array.h forms, one per declared index, rather
    // than under the property's own name, which holds nothing; `width` is then
    // an element's width. Zero for a property that is no array, which is every
    // property whose declaration wrote no unpacked dimension, and every one
    // whose dimension the collector does not model -- a queue or associative
    // one, or a second dimension -- and for a dynamic one, whose count is a
    // fact about the object rather than the class.
    uint32_t array_size = 0;
    int64_t array_lo = 0;
    // §7.5: whether the property's one unpacked dimension is the dynamic `[]`.
    // The object then holds the element count under the key
    // ClassArraySizeKey forms, set by `new[]` (§7.5.1) and by a randomize()
    // that constrains the size (§18.4), and its elements under the element
    // keys from index 0 up to that count.
    bool is_dynamic = false;

    bool IsArray() const { return array_size > 0 || is_dynamic; }
  };
  std::vector<PropertyInfo> properties;

  std::unordered_map<std::string, ModuleItem*> methods;

  std::vector<VTableEntry> vtable;

  // §8.9: static class properties are shared state that changes at run time,
  // even though the type descriptor itself is referenced as const. mutable lets
  // a const ClassTypeInfo* update the shared values.
  mutable std::unordered_map<std::string, Logic4Vec> static_properties;

  // §7.8/§8.9: the entries of each static property declared with an
  // associative dimension, keyed by the property's name and built on the first
  // reference to it (ClassAssocProperty in
  // src/simulator/eval_array_class_assoc.h), §7.8 allocating an associative
  // array no storage until it is used. Shared by every instance, as
  // static_properties is, and mutable for the same reason.
  mutable std::unordered_map<std::string, AssocArrayObject*>
      static_assoc_properties;

  // §7.10/§8.9: the elements of each static property declared with a queue
  // dimension, `static Reg all[$]`, keyed by the property's name and built on
  // the first reference to it (ClassQueueProperty in
  // src/simulator/eval_array_class_queue.h), §7.10 having a queue with no
  // initial value start empty. Shared by every instance, as static_properties
  // is, and mutable for the same reason.
  mutable std::unordered_map<std::string, QueueObject*> static_queue_properties;

  // §15.3.1 and §15.4.1 with §8.9: the semaphore and the mailbox each static
  // property declared `static semaphore s` or `static mailbox mb` holds,
  // keyed by the property's name -- one copy shared by every object of the
  // class, created once, which a method reaches by the bare name, a static
  // method (§8.10) without an object, and the module by `C::mb` or through
  // any handle. Built on the first reference to the property from the
  // declaration's `new` (SemaphoreOfProperty and MailboxOfProperty in
  // src/simulator/eval_class_sync.h) or by a `C::s = new(2)` on it, as
  // static_assoc_properties is built on first use; a property with no entry,
  // or with a null one, is the null handle. Shared as static_properties is,
  // whose entry for the property is the handle's carrier, and mutable for
  // the same reason. Before these maps a static property was left to the
  // run's tables, which hold no class's, so its every method reached nothing.
  mutable std::unordered_map<std::string, SemaphoreObject*>
      static_semaphore_properties;
  mutable std::unordered_map<std::string, MailboxObject*>
      static_mailbox_properties;

  // §18.5.10: a constraint block qualified 'static' has one active/inactive
  // state shared by every instance of the declaring class, rather than a
  // per-object state. constraint_mode() on such a block reads and writes this
  // class-wide map; turning it OFF (or ON) is observed by all instances. Like
  // static_properties it is mutable so a const ClassTypeInfo* can update it.
  mutable std::unordered_map<std::string, bool> static_constraint_active;

  // §18.4.2: when a randc variable is declared static, its cyclic state is
  // static as well — a single permutation sequence is shared by every instance
  // of the declaring class, so randomize() advances that one sequence no matter
  // which instance drives it. The in-progress permutation history of each such
  // member is kept here, keyed by member name; because there is one type
  // descriptor per class, all instances share it. mutable so a const
  // ClassTypeInfo* can advance the shared state, as with static_properties.
  mutable std::unordered_map<std::string,
                             std::shared_ptr<std::unordered_set<int64_t>>>
      static_randc_history;

  std::unordered_map<std::string, uint64_t> enum_members;

  // §18.5.7.1: the relations each foreach iterative constraint of the class
  // instances, once per element of the array it iterates, built the first time
  // an object of the class is randomized over that many elements and kept
  // with the count, a fixed array's shape being a fact about the class and a
  // dynamic array's element count one about the randomize() call (§18.4),
  // which rebuilds the relations when it differs. Keyed by the constraint as
  // the parser recorded it; mutable like static_properties so a const
  // ClassTypeInfo* can fill it.
  struct ForeachInstances {
    uint32_t count = 0;
    std::vector<Expr*> relations;
  };
  mutable std::unordered_map<const ConstraintForeachRef*, ForeachInstances>
      foreach_instances;

  // §18.5.7.1: each constraint relation of the class that names the size
  // method of a dynamic array property, as the relation reads with the call
  // replaced by the identifier of the key the size is held under, which is
  // what a randomize() solves the size as; built on first use and kept, keyed
  // by the relation as the parser recorded it.
  mutable std::unordered_map<const Expr*, Expr*> size_resolved_relations;

  // §37.32: the class specializations that name this class definition as their
  // defining class; reported by the vpiClassTypespec iteration on a class defn.
  std::vector<const ClassTypespecInfo*> direct_specializations;

  // §9.4.2 with §8.9: the processes waiting on a change of a static property
  // of the class -- an event control or a wait whose operand is `C::n`, or the
  // bare `n` inside a method of C. A static property is the class's own
  // storage, static_properties above, which no object's watchers see written:
  // a write to it announces itself here through NotifyStaticWatchers, from
  // every path that stores into that map. The convention is Variable's and
  // ClassObject's: a watcher answering true is retired, one answering false
  // stays armed. mutable as static_properties is, the type descriptor being
  // referenced as const while the watch is armed and fired.
  mutable std::vector<std::function<bool()>> static_watchers;

  void AddStaticWatcher(std::function<bool()> cb) const {
    static_watchers.push_back(std::move(cb));
  }

  void NotifyStaticWatchers() const {
    auto pending = std::move(static_watchers);
    for (auto& cb : pending) {
      if (!cb()) static_watchers.push_back(std::move(cb));
    }
  }

  int FindVTableIndex(std::string_view mname) const;

  bool IsA(const ClassTypeInfo* other) const;

  // §8.13: the property `name` declares in this class or in one it inherits
  // from, the nearest declaration first, or nullptr where none declares it.
  const PropertyInfo* FindProperty(std::string_view name) const;

  // §8.13 (printed pages 189-190) with §8.9 (printed 186): the class on the
  // extends chain from this one whose own storage holds the static property
  // `name` -- the one declaring it, C for `D::n` where D extends C, since a
  // derived class inherits the base's properties and a static property is
  // one storage shared by every object of the class, so `C::n`, `D::n`, a D
  // object's `n` and the bare `n` of D's methods all name C's. Nullptr where
  // none of them declares `name`. Every read, write and watch of a static
  // property goes through this class: static_properties holds a class's own
  // declarations alone, so a site asking D's found no `n`, read 0, wrote
  // nowhere and armed nothing.
  const ClassTypeInfo* StaticPropertyDeclarer(std::string_view name) const;

  // §8.10 and §8.23: the class whose own storage holds the static property a
  // method of this class names bare -- this class or a base it inherits it
  // from (StaticPropertyDeclarer), or else the nearest class lexically
  // containing it or a base of that one, a nested class having unqualified
  // access to the containing class's static properties, local ones included.
  // Nullptr where none of them declares `name`.
  const ClassTypeInfo* StaticPropertyOwner(std::string_view name) const;
};

inline constexpr uint64_t kNullClassHandle = 0;

struct ClassObject {
  const ClassTypeInfo* type = nullptr;
  std::unordered_map<std::string, Logic4Vec> properties;
  // §7.8/§8.5: the entries of each property declared with an associative
  // dimension, keyed by the property's bare name. Such a property holds
  // nothing under `properties`: its elements are allocated one by one as they
  // are first written (§7.8), which is what an AssocArrayObject models, and
  // the object holds one per property, built on the first reference to the
  // property by ClassAssocProperty in src/simulator/eval_array_class_assoc.h.
  // ShallowCopy copies the entries, a property being a variable of the object
  // (§8.12).
  std::unordered_map<std::string, AssocArrayObject*> assoc_properties;
  // §7.10/§8.5: the elements of each property declared with a queue
  // dimension, `Item q[$]` or `T fifo[$:DEPTH-1]`, keyed by the property's
  // bare name. The queue is what §7.10.1's operators and §7.10.2's methods act
  // on, and the object holds one per property, built on the first reference
  // to the property by ClassQueueProperty in
  // src/simulator/eval_array_class_queue.h, or at construction by
  // InitClassQueueProperty where the declaration has an initializer (§8.7).
  // ShallowCopy copies the elements, a property being a variable of the
  // object (§8.12).
  std::unordered_map<std::string, QueueObject*> queue_properties;
  // §15.3.1 and §15.4.1 with §8.7: the semaphore and the mailbox each
  // property declared `semaphore s` or `mailbox mb` holds, keyed by the
  // property's bare name. Either is a built-in class object the property is
  // a handle to, built by the declaration's `new` when the object is
  // constructed (TryInitClassSyncProperty in src/simulator/eval_class_sync.h)
  // or by a later `s = new(2)` on the property, so each object has a bucket
  // and a queue of its own; a property with no entry, or with a null one, is
  // the null handle. ShallowCopy copies the entries as it copies a handle
  // (§8.12), the copy naming the same semaphore or mailbox. Before these
  // maps a property's `new` was evaluated as a value and every method on the
  // property was resolved through the run's own tables by name alone, so a
  // class's mailbox passed nothing and its semaphore held no keys.
  std::unordered_map<std::string, SemaphoreObject*> semaphore_properties;
  std::unordered_map<std::string, MailboxObject*> mailbox_properties;
  // §8.25: the type each type parameter of the class is bound to in the
  // specialization this object was constructed as, keyed by the parameter's
  // name -- `KEY` to `string` for a `uvm_pool #(string, int)` -- as the
  // declaration of the variable the `new` was on wrote the actual
  // (ApplyClassParamOverrides in src/simulator/eval_class_params.cpp binds
  // it). A parameter absent here takes the default the class declares
  // (ClassDecl::param_types), which is §8.25.1's default specialization. The
  // pointed-to types live in the AST, which outlives the run.
  std::unordered_map<std::string, const DataType*> type_param_actuals;
  // §9.4.2: the processes waiting on a change of this object's state -- an
  // event control whose operand is a member of the object, `@(p.status)`
  // through a handle or `@(status)` inside a method. A member write announces
  // itself through SimContext::NotifyClassHandleWatchers, which notifies the
  // variables designating the object and then these, so a process that
  // reached the object through `this` alone, with no variable naming it, is
  // woken too. The convention is Variable's: a watcher answering true is
  // retired, one answering false stays armed.
  std::vector<std::function<bool()>> watchers;

  void AddWatcher(std::function<bool()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    auto pending = std::move(watchers);
    for (auto& cb : pending) {
      if (!cb()) watchers.push_back(std::move(cb));
    }
  }

  uint32_t ref_count = 0;

  // The handle SimContext::AllocateClassObject issued for this object, which is
  // what a design holds in a class variable and what SimContext::GetClassObject
  // takes to get back here. It is recorded on the object because the two places
  // that hold an object without one are reached with no handle to pass:
  // ExecInstanceMethodCall in src/simulator/eval_function.cpp and
  // ConstraintEvalScope in src/simulator/eval_randomize_internal.h both take a
  // ClassObject* and push it as the current `this`, so evaluating a bare `this`
  // to the handle §8.11 says it denotes has to read the handle off the object.
  // kNullClassHandle until the allocation issues one, which every object
  // reaches: the two sites that create a ClassObject, EvalClassNew in
  // src/simulator/eval_function.cpp and ClassObject::ShallowCopy in
  // src/simulator/class_object.cpp, both allocate straight afterwards.
  uint64_t handle = kNullClassHandle;

  // §18.14.1 object stability: every instance owns an independent RNG for its
  // randomization methods. The allocating context installs rng_seed when the
  // object is created -- drawn from the creating thread's stream when one is
  // running, or from the enclosing initialization RNG for objects built by a
  // static declaration initializer (when no thread is active). The generator
  // is materialized lazily on first use so two objects created in the same
  // order from the same starting state always replay the same seeds.
  uint32_t rng_seed = 0;
  std::mt19937 rng;
  bool rng_initialized = false;

  // §18.9: constraint_mode() turns a named constraint block active or inactive
  // for this object. Every block is active when the object is created, so the
  // default (an absent entry) means active; an explicit entry records the state
  // a constraint_mode() call last set. A subsequent randomize() consults this
  // to decide whether each block binds the solve.
  std::unordered_map<std::string, bool> constraint_active;

  // §18.8: rand_mode() turns an individual random variable active or inactive
  // for this object. Every rand/randc variable is active when the object is
  // created, so the default (an absent entry) means active; an explicit entry
  // records the state a rand_mode() call last set. A subsequent randomize()
  // consults this to decide whether each variable is drawn a fresh value or
  // held at its current value as a state variable.
  std::unordered_map<std::string, bool> rand_active;

  // §18.4.2: a randc variable cycles through a random permutation of its
  // declared range, returning each value once before any value repeats; when
  // the permutation is exhausted a fresh one is computed and the iteration
  // restarts. That no-repeat property spans successive randomize() calls, so
  // the set of values already drawn in the current iteration must outlive any
  // single solve. Each randc member's in-progress permutation history is kept
  // here, keyed by member name, and handed to the constraint solver as shared
  // state so the solver advances the same set in place across calls. An entry
  // is created lazily the first time its member is randomized.
  std::unordered_map<std::string, std::shared_ptr<std::unordered_set<int64_t>>>
      randc_history;

  Logic4Vec GetProperty(std::string_view name, Arena& arena) const;

  void SetProperty(std::string_view name, const Logic4Vec& raw);

  ModuleItem* ResolveVirtualMethod(
      std::string_view name, const ClassTypeInfo** owner_out = nullptr) const;

  ModuleItem* ResolveMethod(std::string_view name) const;

  // Resolves `name` starting at `from_type` and walking up the inheritance
  // chain. When `defining_type_out` is non-null, it receives the class in which
  // the method was found (its lexically enclosing class), so callers can track
  // the scope for a subsequent `super` resolution.
  ModuleItem* ResolveMethodForType(
      std::string_view name, const ClassTypeInfo* from_type,
      const ClassTypeInfo** defining_type_out = nullptr) const;

  Logic4Vec GetPropertyForType(std::string_view name,
                               const ClassTypeInfo* declared_type,
                               Arena& arena) const;

  bool BareNameIsDeclaredBy(std::string_view name,
                            const ClassTypeInfo* owner) const;
  void SetPropertyForType(std::string_view name,
                          const ClassTypeInfo* declared_type,
                          const Logic4Vec& raw);

  ClassObject* ShallowCopy(Arena& arena) const;
};

// §37.32: a class typespec is either a purely lexical construct (a typespec
// written in source that names a class) or a class specialization (a concrete
// instantiation of a parameterized class). The two forms support different
// relations, so the kind is modeled explicitly.
enum class ClassTypespecKind : std::uint8_t {
  kLexical,
  kSpecialization,
};

// §37.32: one method visible from a class typespec. has_explicit_decl is false
// for built-in methods that were never declared in source; those are excluded
// when iterating the methods of a specialization.
struct ClassTypespecMethod {
  std::string_view name;
  bool is_static = false;
  bool has_explicit_decl = true;
};

// §37.32: one parameter visible from a class typespec. is_local_param is true
// for parameters declared in the class body (as opposed to the parameter port
// list); it is the value vpi_get(vpiLocalParam) reports for that parameter.
struct ClassTypespecParam {
  std::string_view name;
  bool is_local_param = false;
};

// §37.32: a parameter assignment for a class typespec. vpiRhs reports the
// explicit argument supplied at the specialization site when one is given, and
// otherwise falls back to the parameter's declared default.
struct ClassTypespecParamAssign {
  std::string_view name;
  bool has_explicit_arg = false;
  std::string_view explicit_rhs;
  std::string_view default_rhs;
  // §37.32 detail 3 (printed page 1043 of IEEE 1800-2023): a typespec
  // representing only a lexical construct answers the written expression for
  // vpiRhs, which explicit_rhs and default_rhs carry, but one representing a
  // class specialization may answer any object holding the value the
  // parameter has. True with `bound_value` filled where the type the typespec
  // was built from holds that value, which §8.25 makes a fact about the
  // specialization (VpiClassTypespecOf below).
  bool has_bound_value = false;
  Logic4Vec bound_value;
};

// §37.32: a constraint visible from a class typespec. An inline constraint is
// not part of the typespec's constraint set; an external constraint is ordered
// by its prototype declaration rather than its out-of-body definition.
struct ClassTypespecConstraint {
  std::string_view name;
  bool is_inline = false;
  bool is_extern = false;
  int decl_order = 0;
  int prototype_order = 0;
};

// §37.32: a virtual interface variable of a class typespec. array_size greater
// than zero denotes an array of that many elements; zero denotes a scalar.
struct ClassTypespecVifVar {
  std::string_view name;
  int array_size = 0;
};

// §37.32: lightweight description of a class typespec sufficient to answer the
// VPI queries this clause defines. It reuses ClassTypeInfo for the class
// definition (which already carries the base-class chain and the built-in
// flag).
struct ClassTypespecInfo {
  std::string_view name;
  ClassTypespecKind kind = ClassTypespecKind::kLexical;

  // §37.32: declared lifetime, shared with §37.3.7. False => static.
  bool automatic = false;

  // §37.32: the defining class. May be a built-in class (class_defn then
  // reports NULL) or null when unknown.
  const ClassTypeInfo* class_defn = nullptr;

  // §37.32: the base class typespec this one extends, if any.
  const ClassTypespecInfo* extends = nullptr;

  std::vector<ClassTypespecMethod> methods;
  std::vector<ClassTypespecParam> params;
  std::vector<ClassTypespecConstraint> constraints;
  std::vector<ClassTypespecVifVar> vif_vars;
  std::vector<ClassTypespecParamAssign> param_assigns;
};

// §37.32: a lexical-only typespec does not support the member-collection
// relations (vpiVariables, vpiMethods, vpiConstraint, vpiNamedEvent,
// vpiNamedEventArray, vpiTypedef, vpiInternalScope). Only a specialization
// does.
bool VpiClassTypespecSupportsMembers(const ClassTypespecInfo& ts);

// §37.32: a specialization must carry a valid, non-empty (though tool-chosen)
// name.
bool VpiClassTypespecNameValid(const ClassTypespecInfo& ts);

// §37.32: the defining class returned by the vpiClassDefn relation, or nullptr
// for a built-in class.
const ClassTypeInfo* VpiClassDefnOf(const ClassTypeInfo& cls);

// §37.32: the base class typespec returned by vpiExtends, or nullptr when the
// typespec derives from nothing.
const ClassTypespecInfo* VpiExtendsOf(const ClassTypespecInfo& ts);

// §37.32: the base typespec of a specialization shall itself be a
// specialization. Returns true when this invariant holds for ts (vacuously true
// when ts has no base or ts is not a specialization).
bool VpiClassTypespecBaseIsSpecialization(const ClassTypespecInfo& ts);

// §37.32: the methods reported when iterating vpiMethods on a specialization:
// both static and automatic methods, but excluding built-in methods that have
// no explicit declaration.
std::vector<ClassTypespecMethod> VpiClassTypespecMethods(
    const ClassTypespecInfo& ts);

// §37.32: vpi_get(vpiLocalParam) for a class-typespec parameter -- true when
// the parameter was declared in the class body.
bool VpiClassTypespecParamIsLocal(const ClassTypespecParam& param);

// §37.32: the vpiRhs of a parameter assignment -- the explicit argument when
// one was supplied, otherwise the declared default.
std::string_view VpiClassTypespecParamRhs(const ClassTypespecParamAssign& pa);

// §37.32 detail 1 (printed page 1043 of IEEE 1800-2023): a class typespec
// whose parameter values are all resolved represents a class specialization,
// which the values a class type carries at the run are, so this is the
// typespec of `type` and its kind is kSpecialization. Detail 3 then lets each
// param assignment answer the value the parameter has rather than the
// expression the source wrote, so each carries what
// ClassTypeInfo::static_properties holds for it (§8.25 putting a
// specialization's parameters there, SpecializationOf in
// class_specialization.cpp), and a parameter the type holds no value for
// carries none.
//
// `extends` is left null, a returned value owning no nested typespec: the
// base's is had by asking this of ClassTypeInfo::parent. An empty typespec
// for a null `type` or one with no declaration, a built-in class having none
// and §37.32 having its class_defn report NULL.
ClassTypespecInfo VpiClassTypespecOf(const ClassTypeInfo* type);

// §37.32: a value read through a class typespec is only well defined for static
// members; a non-static member has no value until an instance is selected, so
// access via the typespec alone is disallowed for it.
bool VpiClassTypespecValueAccessAllowed(bool obtained_from_class_typespec,
                                        bool is_static);

// §37.32: the constraints reported when iterating a class typespec -- inline
// constraints are excluded, and the remaining constraints follow declaration
// order, with external constraints ordered by their prototype.
std::vector<ClassTypespecConstraint> VpiClassTypespecConstraints(
    const ClassTypespecInfo& ts);

// §37.32: the number of virtual interface variables when arrays are expanded to
// one entry per element.
int VpiClassTypespecVirtualInterfaceVarCount(const ClassTypespecInfo& ts);

// §37.32: the number of virtual interface variables when each array counts as a
// single collapsed variable.
int VpiClassTypespecArrayVarCount(const ClassTypespecInfo& ts);

// §37.32: the class specializations that directly name this class definition.
std::vector<const ClassTypespecInfo*> VpiClassDefnSpecializations(
    const ClassTypeInfo& cls);

// §8.12: the declared class-type name of property `field` on `type`, searching
// base classes along the parent chain. Empty when no such property exists or it
// is not class-typed. A bare `new` on the right of an assignment carries no
// type of its own -- §8.7 has the left-hand side determine what is constructed
// -- so a caller writing to a class-handle property resolves the type to
// construct through this.
std::string_view MemberClassTypeName(const ClassTypeInfo* type,
                                     std::string_view field);

struct WeakReference {
  uint64_t referent_handle = kNullClassHandle;

  uint64_t Get() const { return referent_handle; }

  void Clear() { referent_handle = kNullClassHandle; }

  static int64_t GetId(uint64_t obj_handle) {
    return (obj_handle == kNullClassHandle) ? 0
                                            : static_cast<int64_t>(obj_handle);
  }
};

}  // namespace delta
