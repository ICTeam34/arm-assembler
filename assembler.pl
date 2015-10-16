use v5.18;

my %req_table;

open INFILE, "<", $ARGV[0] or die "$!";
$ARGV[0] .= ".out";
open TEMP, ">", $ARGV[0] or die "$!";

for (<INFILE>) {
  if (/\.req/) {
    (my $key, my $value) = /([^\s]+)\s+\.req\s+([^\s]+)/;
    $req_table{$key} = $value;
    next;
  }

  if (/\.unreq/) {
    (my $value) = /\.unreq\s+([^\s]+)/; 
    my %rhash = reverse %req_table;
    my $key   = $rhash{$value};
    delete $req_table{$key};
    next;
  }

  my $regex = join "|", keys %req_table;
  $regex = qr/$regex/;

  s/($regex)/$req_table{$1}/g;

  print TEMP; 
}

close INFILE;
close TEMP;

my $args = join ' ', @ARGV;
`./assemble $args`;
