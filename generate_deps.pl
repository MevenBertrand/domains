print "digraph logrel_deps {\n";
# See here for color schemes: https://graphviz.org/doc/info/colors.html
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
# print "  subgraph cluster_autosubst { label=\"AutoSubst\" \n}";
# print "  subgraph cluster_syntax { label=\"Syntax\" \n}";
# print "  subgraph cluster_logrel { label=\"LogicalRelation\" \n}";
# print "  subgraph cluster_subst { label=\"Validity\" \n}";
# print "  subgraph cluster_typing { label=\"TypingProperties\" \n}";
# print "  subgraph cluster_algo { label=\"Algorithmic\" \n}";
# print "  subgraph cluster_check { label=\"Checkers\" \n}";
while (<>) {
  if (m/.*?theories\/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\./rg =~ m/(.*\.)?([^.]*)$/);
    print "\"$path$src\"[label=\"$src\"]" ;
    for my $dest (split(" ", $dests)) {
      $dest =~ s/\//\./g ;
      print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/theories\.(.*)\.vo/);
    }
  }
}
print "}\n";