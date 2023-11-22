#include "./subsat.hpp"


// TODO: move solver implementation here


void subsat::print_config(std::ostream& os)
{
    os << "Features:";
    if (SUBSAT_STANDALONE) { os << " STANDALONE"; }
    if (VDEBUG) { os << " DEBUG"; }
    if (SUBSAT_LOGGING_ENABLED) { os << " LOG"; }
    if (SUBSAT_LEARN) { os << " LEARN"; }
    if (SUBSAT_RESTART) { os << " RESTART(" << SUBSAT_RESTART_INTERVAL << ")"; }
    if (SUBSAT_MINIMIZE) { os << " MINIMIZE"; }
    if (SUBSAT_VDOM) { os << " VDOM"; }
    if (SUBSAT_VMTF) { os << " VMTF"; }
    if (SUBSAT_VMTF_BUMP) { os << " VMTF_BUMP"; }
    if (SUBSAT_PHASE_SAVING) { os << " PHASE_SAVING"; }
    if (SUBSAT_SIMPLIFY_CLAUSES) { os << " SIMPLIFY_CLAUSES"; }
    if (SUBSAT_SIMPLIFY_AMOS) { os << " SIMPLIFY_AMOS"; }
    if (SUBSAT_STATISTICS) { os << " STATS"; }
    if (VDEBUG && SUBSAT_EXPENSIVE_ASSERTIONS) { os << " EXPENSIVE_ASSERTIONS"; }
    os << '\n';
}
