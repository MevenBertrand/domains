print "digraph logrel_deps {\n";
# See here for color schemes: https://graphviz.org/doc/info/colors.html
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
print "  subgraph cluster_categories { label=\"categories\" \n}";
print "  subgraph cluster_utils { label=\"utils\" \n}";
while (<>) {
  if (m/.*?theories\/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\./rg =~ m/(.*\.)?([^.]*)$/);
    if ($path =~ m/categories\./) {
      print "subgraph cluster_categories { \"$path$src\"[label=\"$src\",fillcolor=1]}"
    }elsif ($path =~ m/utils\./) {
      print "subgraph cluster_utils { \"$path$src\"[label=\"$src\",fillcolor=2]}"
    }else {
      print "\"$path$src\"[label=\"$src\",fillcolor=6,fontcolor=white]"
    }
    for my $dest (split(" ", $dests)) {
      $dest =~ s/\//\./g ;
      print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/theories\.(.*)\.vo/);
    }
  }
}
print "}\n";