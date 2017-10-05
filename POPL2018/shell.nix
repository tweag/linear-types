# Non-reproducible "current" version:
# with (import <nixpkgs> {});
# This works for RRN:
# with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-16.09.tar.gz) {};
# with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-17.03.tar.gz) {};
with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-17.09.tar.gz) {};

let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
in stdenv.mkDerivation {
  name = "docsEnv";
  buildInputs = [ # orgEmacs
                  haskellPackages.lhs2tex
                  biber
                  pdftk
                  zip
                  (texlive.combine {
                       inherit (texlive)
                       algorithm2e
                       biblatex
                       boondox
                       cmll
                       collection-fontsrecommended
                       comment
                       environ
                       fontaxes
                       inconsolata
                       kastrup
                       latexmk
                       libertine
                       listings
                       lm
                       logreq
                       mweights
                       ncclatex
                       ncctools
                       newtx
                       newtxsf
                       newtxtt
                       newunicodechar
                       prftree
                       relsize
                       scheme-small wrapfig marvosym wasysym
                       stmaryrd lazylist polytable
                       todonotes
                       totpages
                       trimspaces
                       ucs
                       wasy cm-super unicode-math filehook lm-math capt-of
                       xargs
                       xstring ucharcat;
                     })
                ];
}
