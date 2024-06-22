\ProvidesClass{slides}[15/10/2021 Lecture and Talk format]

\LoadClass[aspectratio=169]{beamer} %[aspectratio=169]
\RequirePackage{xcolor}
\RequirePackage{minted}
\RequirePackage[sfdefault, light]{FiraSans}
\RequirePackage{tikz}
\RequirePackage[framemethod=TikZ]{mdframed}
% \RequirePackage{FiraMono}

\usetheme{metropolis}
\usepackage{charcoaltoothpaste}
\usemintedstyle{material}

\newmintinline[scala]{scala}{fontsize=\normalsize}
\newmintinline[haskell]{haskell}{fontsize=\normalsize}
\newmintinline[java]{java}{fontsize=\normalsize}
\newmintinline[kotlin]{kotlin}{fontsize=\normalsize}
\newmintinline[rust]{rust}{fontsize=\normalsize}

\definecolor{Mint}{RGB}            { 113, 206, 172 }
\definecolor{MintCream}{RGB}       { 220, 255, 237 }
\definecolor{DarkCharcoalGrey}{RGB}{ 32,  32,  37  }
\definecolor{CharcoalGrey}{RGB}    { 46,  47,  48  }

\usetikzlibrary{shapes}
\tikzstyle{Type}=[fill=CharcoalGrey, draw=MintCream, shape=ellipse, text=white]
\tikzstyle{Inherits}=[-stealth, draw=MintCream]

\RequirePackage{pifont}% http://ctan.org/pkg/pifont

\newcommand{\cmark}{\textcolor{OwlGreen}{\ding{51}}}%
\newcommand{\xmark}{\textcolor{OwlRed}{\ding{55}}}%

\newenvironment{codebox}[1]
  {\mdfsetup{
    linecolor=Mint,
    backgroundcolor=DarkCharcoalGrey,
    roundcorner=4pt,
    frametitle={\colorbox{DarkCharcoalGrey}{\space\textcolor{Mint}{\scriptsize{#1}}\space}},
    innertopmargin=-4pt,
    frametitleaboveskip=-.7\ht\strutbox,
    frametitlealignment=\center
    }
  \begin{mdframed}%
  }
  {\end{mdframed}}

\author{Jordan Hall}
\institute{Imperial College London}