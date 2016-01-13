angular.module('keymaerax.controllers').controller('ModelUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, $route, $uibModal, Models) {

     $scope.runPreloadedProof = function(model) {
        $http.post("/models/users/" + $scope.userId + "/model/" + model.id + "/initialize")
            .success(function(data) {
                if(data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Proof Preloader")
                } else {
                    console.log("yay! Take the user to the proof load page?")
                }
            })
     };

     $scope.addModel = function() {
          var file = keyFile.files[0];

          var fr = new FileReader();
          fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); };
          fr.onload = function(e) {
            $http.post("user/" + $cookies.get('userId') + "/modeltextupload/" + $scope.modelName, e.target.result)
              .then(function(response) {
                if (response.data.type === 'parseerror') {
                  $uibModal.open({
                     templateUrl: 'templates/parseError.html',
                     controller: 'ParseErrorCtrl',
                     size: 'lg',
                     resolve: {
                        model: function () { return e.target.result; },
                        error: function () { return response.data; }
                     }});
                } else {
                   //Update the models list -- this should result in the view being updated?
                   while (Models.getModels().length != 0) {
                      Models.getModels().shift()
                   }
                   $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
                     Models.addModels(data);
                     $route.reload();
                   });
                }
              })
          };

          fr.readAsText(file);
     };

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $cookies, $uibModal, $location, Models) {
  $scope.models = [];
  $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
      $scope.models = data
  });

  $scope.open = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeldialog.html',
        controller: 'ModelDialogCtrl',
        size: 'lg',
        resolve: {
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.openTactic = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeltacticdialog.html',
        controller: 'ModelTacticDialogCtrl',
        size: 'lg',
        resolve: {
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.runTactic = function (modelid) {
    $http.post("user/" + $cookies.get('userId') + "/model/" + modelid + "/tactic/run")
    .success(function(data) {
        if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Error While Running Tactic")
        else console.log("Done running tactic")
    });
  }

  $scope.$watch('models',
      function (newModels) { if (newModels) Models.setModels(newModels); }
  );
  $scope.$emit('routeLoaded', {theview: 'models'});
})

angular.module('keymaerax.controllers').controller('ModelDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid).success(function(data) {
      $scope.model = data
  });

  $scope.ok = function () { $modalInstance.close(); };
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid + "/tactic").success(function(data) {
      $scope.tactic = data
  });

  $scope.ok = function () { $modalInstance.close(); };
});