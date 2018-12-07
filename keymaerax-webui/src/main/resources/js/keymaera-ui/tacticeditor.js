angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete'])
  .directive('k4TacticEditor', ['$http', '$sce', 'derivationInfos', 'Textcomplete', 'sequentProofData', 'TextHighlighter',
      function($http, $sce, derivationInfos, Textcomplete, sequentProofData, TextHighlighter) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            highlightTactics: '=?',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onTacticScript: '&',
            onTacticEdit: '&',
        },
        link: function(scope, elem, attr) {
          var tacticContent = elem.find('.k4-tactic-area');

          scope.tactic = sequentProofData.tactic;
          scope.tacticError = {
            error: "",
            details: "",
            isVisible: false
          }

          scope.getRows = function(text) {
            return (text.match(/\n/g) || '').length + 1
          }

          scope.$watchGroup(['tactic.tacticText', 'highlightTactics', 'tactic.selectedTacticId'], function() {
            var h = new TextHighlighter();
            var tactic = sequentProofData.tactic;
            var tree = sequentProofData.proofTree;
            if (tactic.tacticText !== tactic.lastExecutedTacticText) {
              //@todo Highlight modified tactics
              tactic.highlightedText = ''
              return
            }
            var regions = []
            for (var id = scope.nodeId, started = false; id; ) {
              started = h.addNode(id, 'active-tactic' + (!started ? ' last-tactic' : '')) || started;
              var node = tree.node(id);
              id = node && node.parent;
            }
            $.each(scope.highlightTactics || [], function(i, nodeId) { h.addNode(nodeId, 'extra-tactic'); });
            h.addNode(tactic.selectedTacticId, 'selected-tactic')
            tactic.highlightedText = h.highlight(tactic.tacticText)
          });

          scope.updateSelection = function() {
            var point = scope.tactic.selectionStart = tacticContent.prop('selectionStart')
            // Find first tactic ending after point
            var lo = 0, hi = scope.tactic.tacticLocators.length;
            while (lo < hi) {
              var mid = lo + ((hi - lo) >> 1);
              var midLocator = scope.tactic.tacticLocators[mid];
              if (midLocator.end < point) {
                lo = mid + 1;
              } else {
                hi = mid;
              }
            }
            var locator = scope.tactic.tacticLocators[lo];
            scope.tactic.selectedTacticId = locator && locator.node;
          }

          var combinators = ['*', '|', ';', '<'];
          var textComplete = new Textcomplete(tacticContent, [
            // combinators
            {
              match: /\B:(\w*)$/,
              search: function (term, callback) {
                callback($.map(combinators, function (element) {
                    return element.indexOf(term) === 0 ? element : null;
                }));
              },
              index: 1,
              replace: function (element) { return element; }
            },
            // positions 1.0.tactic
            {
                match: /(((\-?[1-9]([0-9]*)\.)([0-1]\.)*)(\w*))$/,
                search: function (term, callback) {
                  var dotPos = term.lastIndexOf('.');
                  var keyword = term.substring(dotPos + 1);
                  this.position = term.substring(0, dotPos);
                  // other code for some reason uses , as separator
                  var formulaId = this.position.replace(/\./g, ',');
                  sequentProofData.formulas.highlighted = formulaId.indexOf(',') >= 0 ? formulaId : formulaId + ','; //@note top-level formula IDs end in ','
                  //console.log("Matched term " + term + ", searching for keyword " + keyword + "; position " + this.position);
                  $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/list')
                       .success(function(data) {
                    sequentProofData.tactic.currentSuggestions = data;
                    callback($.map(data, function (element) {
                      return element.standardDerivation.id.indexOf(keyword) === 0 ? element.standardDerivation.id : null;
                    }));
                  });
                },
                index: 2,
                replace: function (element) {
                  var di = $.grep(sequentProofData.tactic.currentSuggestions, function(e, i) { return e.standardDerivation.id === element })[0];
                  sequentProofData.tactic.currentSuggestions = undefined;
                  sequentProofData.formulas.highlighted = undefined;

                  if (di.standardDerivation.derivation.input == undefined || di.standardDerivation.derivation.input.length == 0) {
                    // tactic without inputs -> execute right away
                    //scope.onTactic({formulaId: this.position, tacticId: element});
                    //return ['<' + element + '>', '</' + element + '>'];
                    return element + "(" + this.position + ")";
                  } else {
                    // tactic with input -> postpone and wait for arguments
                    var inputStrings = $.map(di.standardDerivation.derivation.input, function(e, i) {
                      return "{`" + e.param + ":" + e.type + "`}";
                    });
                    var inputString = inputStrings[0];
                    for (i = 1; i < inputStrings.length; i++) { inputString = inputString + ", " + inputStrings[i]; }
                    return [ element + "(" + inputString, ", " + this.position + ")"];
                  }
                }
            }
          ]);

          scope.executeTacticDiff = function(stepwise) {
            if (scope.tactic.lastExecutedTacticText === scope.tactic.tacticText && scope.tactic.tacticDel === '' 
                  || scope.tactic.tacticDel === 'nil') {
              scope.onTacticScript({tacticText: scope.tactic.tacticDiff, stepwise: stepwise});
            } else {
              //todo prune deleted stuff instead of rerun from root
              var tactic = scope.tactic.tacticText;
              scope.onTacticEdit({tacticText: tactic, stepwise: stepwise});
            }
          };

          var tacticDiffRequestTimer = undefined;

          scope.$watch('tactic.tacticText', function(newValue, oldValue) {
            var newText = jQuery('<p>'+newValue+'</p>').text(); // strip HTML tags
            var oldText = jQuery('<p>'+oldValue+'</p>').text();
            if (oldText !== newText && scope.tactic.lastExecutedTacticText && scope.tactic.tacticText && scope.tactic.lastExecutedTacticText !== scope.tactic.tacticText) {
              //@note compute diff
              var diffInput = { 'old' : scope.tactic.lastExecutedTacticText, 'new' : newText };
              if (tacticDiffRequestTimer) clearTimeout(tacticDiffRequestTimer);
              tacticDiffRequestTimer = setTimeout(requestDiff, 1000);
              function requestDiff() {
                $http.post('proofs/user/' + scope.userId + '/' + scope.proofId + '/tacticDiff', diffInput)
                  .then(function(response) {
                    scope.tacticError.isVisible = false;
                    if (newText !== scope.tactic.tacticText) return;

                    //@todo multiple diffs
                    scope.tactic.tacticDel = response.data.replOld.length > 0 ? response.data.replOld[0].repl : "";
                    scope.tactic.tacticDiff = response.data.replNew.length > 0 ? response.data.replNew[0].repl : "";
//                  var formattedTactic = response.data.context;
//                  $.each(response.data.replNew, function(i, e) {
//                    var old = $.grep(response.data.replOld, function(oe, i) { return oe.dot == e.dot; });
//                    formattedTactic = old.length > 0 ?
//                      formattedTactic.replace(e.dot, '<span class="k4-tacticeditor-repl" title="Replaces ' + old[0].repl + '">' + e.repl + '</span>') :
//                      formattedTactic.replace(e.dot, '<span class="k4-tacticeditor-new">' + e.repl + '</span>');
//                  });
//                  scope.tactic.tacticText = formattedTactic;
                  })
                  .catch(function(response) {
                    if (newText !== scope.tactic.tacticText) return;
                    if (response.data !== undefined) {
                      var errorText = response.data.textStatus;
                      var location = response.data.location; // { column: Int, line: Int }
                      scope.tacticError.text = location.line + ':' + location.column + " " + errorText;
                      scope.tacticError.isVisible = true;
//                    var unparsableStart = newText.split('\n', location.line-1).join('\n').length + location.column-1;
                    //@todo location end
//                    scope.tactic.tacticText = newText.substring(0, unparsableStart) +
//                      '<span class="k4-tacticeditor-error" title="' + errorText + '">' +
//                      newText.substring(unparsableStart, newText.length) + '</span>'
                    }
                  });
              }
            }
          });

          $(textComplete).on({
            'textComplete:select': function(e, value) {
              scope.$apply(function() {
                sequentProofData.tactic.tacticText = value
              })
            },
            'textComplete:show': function(e) {
              $(this).data('autocompleting', true);
            },
            'textComplete:hide': function(e) {
              $(this).data('autocompleting', false);
            }
          });
        },
        template: '<div class="row"><div class="col-md-12">' +
                    '<div class="k4-tactic-backdrop"><div class="k4-tactic-highlights" ng-bind-html="tactic.highlightedText"></div></div>' +
                    '<textarea class="k4-tactic-area" ng-model="tactic.tacticText" ' +
                        'ng-shift-enter="executeTacticDiff(true)" ng-trim="false" ' +
                        'rows="{{ getRows(tactic.tacticText) }}" spellcheck="false" ' +
                        'ng-click="updateSelection()" ng-keyup="updateSelection()"></textarea>' +
                  '</div></div>' +
                  '<div class=row><div class="col-md-12">' +
                  '<k4-auto-hide-alert message="tacticError.text"' +
                                      'details="tacticError.details"' +
                                      'is-visible="tacticError.isVisible" timeout="-1">' +
                  '</k4-auto-hide-alert>' +
                  '</div></div>'
    };
  }]);

angular.module('keymaerax.ui.tacticeditor')
  .factory('TextHighlighter', ['sequentProofData', '$sce', function(sequentProofData, $sce) {
    var tactic = sequentProofData.tactic;

    function TextHighlighter() {
      this.regions = [];
      this.nodes = {};
    }

    function html5Entities(value) {
      return value.replace(/[\u00A0-\u9999<>\&\'\"]/gim, function(i) {
        return '&#' + i.charCodeAt(0) + ';'
      })
    }

    function nodesToRegions(nodes) {
      var regions = [];
      $.each(nodes, function(nodeId, classes) {
        var loc = tactic.tacticLocatorMap[nodeId];
        if (loc) {
          regions.push({
            location: loc,
            classes: classes,
          });
        }
      });
      return regions;
    }

    TextHighlighter.prototype.addNode = function(nodeId, classes) {
      this.nodes[nodeId] = (this.nodes[nodeId] || '') + ' ' + classes;
      return !!tactic.tacticLocatorMap[nodeId];
    }

    TextHighlighter.prototype.highlight = function(text) {
      var regions = nodesToRegions(this.nodes);
      regions.sort(function(a, b) {
        return a.location.start - b.location.start;
      });

      var result = ''
      for (var i = 0, rj = 0, highlighting = false; i < text.length; ++i) {
        while (rj < regions.length && regions[rj].location.end <= i) {
          if (highlighting) {
            result += '</mark>'
            highlighting = false
          }
          rj++;
        }
        var region = regions[rj];
        if (!highlighting && region !== undefined && region.location.start <= i) {
          result += '<mark class="' + region.classes + '">'
          highlighting = true
        }
        result += html5Entities(text[i])
      }

      if (highlighting) {
        result += "</mark>";
      }

      return $sce.trustAs($sce.HTML, result)
    }

    return TextHighlighter;
  }]);
