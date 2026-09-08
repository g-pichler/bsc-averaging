# Why the Comparator configuration lives here

`comparator.json` in this directory is the single Comparator configuration for
this repository. It selects all three theorems and refers to `Submission.lean`
and `Solutions.lean` at the repository root; nothing else lives under
`Submission/`.

The path is what it is because the Palomar Registry keys a registered entry on
the triple

    (source repository, project path, Comparator configuration path)

so the configuration path is part of the identity of an entry, not merely a
location in the tree. Entry `PALOMAR-2026-08-26-000006` was registered from
`Submission/MO285151/comparator.json`, back when the repository carried one
configuration per result and this one selected only

    BSCAveraging.MO285151.averaged_bsc_maximise_mutual_information

Later versions of that entry must be submitted from the same path.

