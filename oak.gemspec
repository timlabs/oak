Gem::Specification.new {|s|
  s.name     = 'oakproof'
  s.version  = '0.7.2'
  s.date     = '2024-06-22'
  s.summary  = 'A proof checker focused on simplicity, readability, and ' +
               'ease of use.'
  s.license  = 'AGPL-3.0'
  s.author   = 'Tim Smith'
  s.homepage = 'https://oakproof.org/'
  s.metadata = {
    'homepage_uri'      => s.homepage,
    'source_code_uri'   => 'https://github.com/timlabs/oak',
    'documentation_uri' => 'https://oakproof.org/tutorial.html',
  }

  s.required_ruby_version = '>= 2.0'

  s.files = Dir['src/*'] + Dir['eprover/*']

  s.bindir = '.'
  s.executables << 'oak'
}