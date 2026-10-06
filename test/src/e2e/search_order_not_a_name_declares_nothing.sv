// A source of comments alone declares nothing, and simulating it on its own runs
// nothing and passes. The -L entry this run names is not a library name, which
// stops the run before anything is elaborated, and that stop fails the run
// whatever the source declares.
