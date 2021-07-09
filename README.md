# Geometric complexity
This repository contains the code for the analyses of

Novak & Stouffer (in review) *Geometric complexity and the information-theoretic comparison of functional-response models.* bioRxiv

Please email Mark Novak (mark.novak@oregonstate.edu) and Daniel Stouffer (daniel.stouffer@canterbury.ac.nz) with any questions.

## Organization
All analyses were performed in Mathematica _v. 12.1.1.0_ using its notebook (_.nb_) format.

#### [code](code/)
The notebooks for recreating the main analyses and figures of the paper are:
- _GeomComp_Compute.nb_ computes the geometric complexities of all considered models for all considered experimental designs of the specified design-type.
- _GeomComp_Plotting.nb_ produces the visualizations of the paper's main results.

The two notebooks are used repeatedly for each experimental design type (i.e. for analyzing logarithmic (= _GoldenRatio_) or _Arithmetic_ prey and predator abundance spacings) as well as for the analyses using alternative minimum or maximum number-of-prey-eaten constraints. Which design type or prey-eaten constraint is to be analyzed is specified manually at the top of the _GeomComp_Compute.nb_ notebook (for design type) or in the argument of the _GeomComplex[]_ function (for the prey-eaten constraint) defined in that notebook.  Which results are to be plotted by _GeomComp_Plotting.nb_ is specified by changing the directory locations of the results and export folders.

Additional notebooks:
- _ParamComp_2ndTerm.nb_ produces Fig. 1 visualizing FIA's parametric complexity term as a function of sample size.
- _GeomComp_H2MM.nb_ produces Fig. 2 comparing Holling and Michaelis-Menten formulations.
- _Identifiability.nb_ produces Fig. S.1 visualizing the identifiability of all considered models as a function of experimental design.

Further notebooks in the [other](code/other) directory were used for visualizing or exploring specific functional-response models or were useful in the development of the primary analyses.

#### [docs](docs)
The [docs](docs) directory contains _pdf_ printouts of the Mathematica notebook files.

#### [figs](figs)
The [figs](figs) directory contains all figures of the main text and supplementary materials, organized by design type.


#### [results](results)
The [results](results) directory contains all files in _.txt_ format exported by _GeomComp_Compute.nb_, organized by design type. The results include the geometric complexity estimates for each model.  The directory also includes _Design___._txt_ files that summarize all considered experimental designs (i.e. prey and predator abundance combinations) as depicted in the paper's supplementary materials.





### Warranty
All code is provided "as is" and without warranty.  If you know of more efficient or elegant ways of doing anything (of which there are most definitely many), we’d love to learn from you.
