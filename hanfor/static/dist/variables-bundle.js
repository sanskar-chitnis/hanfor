!function(e){function a(a){for(var n,i,l=a[0],s=a[1],c=a[2],d=0,_=[];d<l.length;d++)i=l[d],r[i]&&_.push(r[i][0]),r[i]=0;for(n in s)Object.prototype.hasOwnProperty.call(s,n)&&(e[n]=s[n]);for(u&&u(a);_.length;)_.shift()();return o.push.apply(o,c||[]),t()}function t(){for(var e,a=0;a<o.length;a++){for(var t=o[a],n=!0,l=1;l<t.length;l++){var s=t[l];0!==r[s]&&(n=!1)}n&&(o.splice(a--,1),e=i(i.s=t[0]))}return e}var n={},r={4:0},o=[];function i(a){if(n[a])return n[a].exports;var t=n[a]={i:a,l:!1,exports:{}};return e[a].call(t.exports,t,t.exports,i),t.l=!0,t.exports}i.m=e,i.c=n,i.d=function(e,a,t){i.o(e,a)||Object.defineProperty(e,a,{enumerable:!0,get:t})},i.r=function(e){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},i.t=function(e,a){if(1&a&&(e=i(e)),8&a)return e;if(4&a&&"object"==typeof e&&e&&e.__esModule)return e;var t=Object.create(null);if(i.r(t),Object.defineProperty(t,"default",{enumerable:!0,value:e}),2&a&&"string"!=typeof e)for(var n in e)i.d(t,n,function(a){return e[a]}.bind(null,n));return t},i.n=function(e){var a=e&&e.__esModule?function(){return e.default}:function(){return e};return i.d(a,"a",a),a},i.o=function(e,a){return Object.prototype.hasOwnProperty.call(e,a)},i.p="";var l=window.webpackJsonp=window.webpackJsonp||[],s=l.push.bind(l);l.push=a,l=l.slice();for(var c=0;c<l.length;c++)a(l[c]);var u=s;o.push([216,0]),t()}({216:function(e,a,t){(function(e){t(17),t(10),t(15),t(14),t(20),t(13),t(12);let a=["CONST","ENUM"],n=sessionStorage.getItem("var_search_string"),r=[];function o(a){!0===a?e("#variable_value_form_group").hide():e("#variable_value_form_group").show()}function i(a,t=!1){let n=e("body");n.LoadingOverlay("show");let r=e("#multi-change-type-input").val().trim(),o=[];a.rows({selected:!0}).every(function(){let e=this.data();o.push(e.name)}),e.post("api/var/multi_update",{change_type:r,selected_vars:JSON.stringify(o),del:t},function(e){n.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):location.reload()})}function l(){e(".requirement_var_group").each(function(){e(this).hide()}),e(".formalization_card").each(function(a){const t=e(this).attr("title"),n=e("#requirement_scope"+t).val(),r=e("#requirement_pattern"+t).val();let o=e("#requirement_var_group_p"+t),i=e("#requirement_var_group_q"+t),l=e("#requirement_var_group_r"+t),s=e("#requirement_var_group_s"+t),c=e("#requirement_var_group_t"+t),u=e("#requirement_var_group_u"+t);switch(n){case"BEFORE":case"AFTER":o.show();break;case"BETWEEN":case"AFTER_UNTIL":o.show(),i.show()}switch(r){case"Absence":case"Universality":case"Existence":case"BoundedExistence":l.show();break;case"Invariant":case"Precedence":case"Response":case"MinDuration":case"MaxDuration":case"BoundedRecurrence":l.show(),s.show();break;case"PrecedenceChain1-2":case"PrecedenceChain2-1":case"ResponseChain1-2":case"ResponseChain2-1":case"BoundedResponse":case"BoundedInvariance":case"TimeConstrainedInvariant":l.show(),s.show(),c.show();break;case"ConstrainedChain":case"TimeConstrainedMinDuration":case"ConstrainedTimedExistence":l.show(),s.show(),c.show(),u.show();break;case"NotFormalizable":o.hide(),i.hide()}})}function s(){e(".formalization_card").each(function(a){const t=e(this).attr("title");let n="";const o=e("#requirement_scope"+t).find("option:selected").text().replace(/\s\s+/g," "),i=e("#requirement_pattern"+t).find("option:selected").text().replace(/\s\s+/g," ");"None"!==o&&"None"!==i&&(n=o+", "+i+".");let l=e("#formalization_var_p"+t).val(),s=e("#formalization_var_q"+t).val(),c=e("#formalization_var_r"+t).val(),u=e("#formalization_var_s"+t).val(),d=e("#formalization_var_t"+t).val(),_=e("#formalization_var_u"+t).val();l.length>0&&(n=n.replace(/{P}/g,l)),s.length>0&&(n=n.replace(/{Q}/g,s)),c.length>0&&(n=n.replace(/{R}/g,c)),u.length>0&&(n=n.replace(/{S}/g,u)),d.length>0&&(n=n.replace(/{T}/g,d)),_.length>0&&(n=n.replace(/{U}/g,_)),e("#current_formalization_textarea"+t).val(n);let p=e("#formalization_heading"+t);if(t in r)for(let a=0;a<r[t].length;a++)e("#formalization_var_"+r[t][a]+t).addClass("type-error"),p.addClass("type-error-head");else p.removeClass("type-error-head")}),e("#variable_constraint_updated").val("true")}function c(){e(".formalization_selector").change(function(){l(),s()}),e(".reqirement-variable, .req_var_type").change(function(){s()}),e(".delete_formalization").confirmation({rootSelector:".delete_formalization"}).click(function(){!function(a){let t=e(".modal-content");t.LoadingOverlay("show");const n=e("#variable_name").val();e.post("api/var/del_constraint",{name:n,constraint_id:a},function(a){t.LoadingOverlay("hide",!0),!1===a.success?alert(a.errormsg):e("#formalization_accordion").html(a.html)}).done(function(){l(),s(),c()})}(e(this).attr("name"))})}function u(a=!1){!0===a?e(".enum-controls").hide():e(".enum-controls").show()}function d(t){let n=e("#variables_table").DataTable().row(t).data(),i=e(".modal-content");o(!0),u(!0),e("#variable_modal").modal("show"),e("#modal_associated_row_index").val(t),e("#variable_name_old").val(n.name),e("#variable_type_old").val(n.type),e("#occurences").val(n.used_by),e("#variable_modal_title").html("Variable: "+n.name),e("#variable_name").val(n.name);let d=e("#variable_type"),p=e("#variable_value"),m=e("#variable_value_old");var v;d.val(n.type),p.val(""),m.val(""),"CONST"===n.type||"ENUMERATOR"===n.type?(o(),p.val(n.const_val),m.val(n.const_val)):"ENUM"===n.type&&(u(),e("#enumerators").html(""),v=n.name,e.post("api/var/get_enumerators",{name:v},function(a){!1===a.success?alert(a.errormsg):(console.log(a.enumerators),e.each(a.enumerators,function(e,a){_(a[0].substr(v.length+1),a[1])}))}).done(function(){l(),s(),c()})),d.autocomplete({minLength:0,source:a}).on("focus",function(){e(this).keydown()}),function(a){e.post("api/var/get_constraints_html",{name:a},function(a){!1===a.success?alert(a.errormsg):(r=a.type_inference_errors,e("#formalization_accordion").html(a.html))}).done(function(){l(),s(),c()})}(n.name),i.LoadingOverlay("hide")}function _(a,t){const n=`\n        <div class="input-group enumerator-input">\n            <span class="input-group-addon">Name</span>\n            <input class="form-control enum_name_input" type="text" value="${a}">\n            <span class="input-group-addon">Value</span>\n            <input class="form-control enum_value_input" type="number" value="${t}">\n        </div>`;e("#enumerators").append(n)}e(document).ready(function(){let t=e("#variables_table").DataTable({paging:!0,stateSave:!0,select:{style:"os",selector:"td:first-child"},pageLength:50,responsive:!0,lengthMenu:[[10,50,100,500,-1],[10,50,100,500,"All"]],dom:'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',ajax:"api/var/gets",deferRender:!0,columns:[{orderable:!1,className:"select-checkbox",targets:[0],data:null,defaultContent:""},{data:"name",targets:[1],render:function(e,a,t,n){return result='<a class="modal-opener" href="#">'+e+"</span></br>",result}},{data:"type",targets:[2],render:function(e,t,n,r){return null!==e&&a.indexOf(e)<=-1&&a.push(e),null!==e&&"CONST"===e&&(e=e+" ("+n.const_val+")"),e}},{data:"used_by",targets:[3],render:function(a,t,n,r){let o="";return e.inArray("Type_inference_error",n.tags)>-1&&(o+='<span class="badge badge-danger"><a href="#" class="variable_link" data-name="'+n.name+'" >Has type inference error</a></span> '),e(a).each(function(e,a){if(a.length>0){let e=function(e){let a=null,t=/^(Constraint_)(.*)(_[0-9]+$)/gm.exec(e);return null!==t&&(a=t[2]),a}(a);if(null!==e)o+='<span class="badge badge-success"><a href="#" class="variable_link" data-name="'+e+'" >'+a+"</a></span> ";else{o+='<span class="badge badge-info"><a href="./'+("?command=search&col=2&q="+a)+'" target="_blank">'+a+"</a></span> "}}}),o.length<1&&(o+='<span class="badge badge-warning"><a href="#">Not used</a></span></br>'),o}},{data:"used_by",targets:[4],visible:!1,searchable:!1,render:function(a,t,n,r){return result="",e(a).each(function(e,a){a.length>0&&(result.length>1&&(result+=", "),result+=a)}),result}}],initComplete:function(){e("#search_bar").val(n),e(".variable_link").click(function(a){a.preventDefault(),d(function(a){let t=-1;return e("#variables_table").DataTable().row(function(e,n,r){n.name===a&&(t=e)}),t}(e(this).data("name")))})}});t.column(3).visible(!0),t.column(4).visible(!1),e("#search_bar").keyup(function(){t.search(e(this).val()).draw(),sessionStorage.setItem("var_search_string",e(this).val())}),e("#variables_table").find("tbody").on("click","a.modal-opener",function(a){a.preventDefault(),d(t.row(e(a.target).parent()).index())}),e("#save_variable_modal").click(function(){!function(t){let n=e(".modal-content");n.LoadingOverlay("show");const r=e("#variable_name").val(),o=e("#variable_name_old").val(),i=e("#variable_type").val(),l=e("#variable_type_old").val(),s=parseInt(e("#modal_associated_row_index").val()),c=e("#occurences").val(),u=e("#variable_value").val(),d=e("#variable_value_old").val(),_=e("#variable_constraint_updated").val();let p={};e(".formalization_card").each(function(a){let t={};t.id=e(this).attr("title"),e(this).find("select").each(function(){e(this).hasClass("scope_selector")&&(t.scope=e(this).val()),e(this).hasClass("pattern_selector")&&(t.pattern=e(this).val())}),t.expression_mapping={},e(this).find("textarea.reqirement-variable").each(function(){""!==e(this).attr("title")&&(t.expression_mapping[e(this).attr("title")]=e(this).val())}),p[t.id]=t}),null!==i&&a.indexOf(i)<=-1&&a.push(i);let m=[];"ENUM"===i&&e(".enumerator-input").each(function(a,t){let n=e(this).find(".enum_name_input").val(),r=e(this).find(".enum_value_input").val();m.push([n,r])}),e.post("api/var/update",{name:r,name_old:o,type:i,const_val:u,const_val_old:d,type_old:l,occurrences:c,constraints:JSON.stringify(p),updated_constraints:_,enumerators:JSON.stringify(m)},function(a){n.LoadingOverlay("hide",!0),!1===a.success?alert(a.errormsg):a.rebuild_table?location.reload():(t.row(s).data(a.data).draw(),e("#variable_modal").modal("hide"))})}(t)}),e("#variable_type").on("keyup change autocompleteclose",function(){"CONST"===e(this).val()?o():o(revert=!0)}),e(".import_link").on("click",function(){!function(a,t){let n=e("#variable_import_modal");e("#variable_import_sess_name").val(a),e("#variable_import_sess_revision").val(t),e("#variable_import_modal_title").html("Import from Session: "+a+" at: "+t),n.modal("show"),n.LoadingOverlay("show"),e.post("api/var/var_import_info",{sess_name:a,sess_revision:t},function(a){n.LoadingOverlay("hide",!0),!1===a.success?alert(a.errormsg):(e("#import_tot_number").html("Total:\t"+a.tot_vars+" Variables."),e("#import_new_number").html("New:\t"+a.new_vars+" Variables."))})}(e(this).attr("data-name"),e(this).attr("data-revision"))}),e("#save_variable_import_modal").click(function(a){!function(){let a=e("#variable_import_modal"),t=e("#variable_import_sess_name").val(),n=e("#variable_import_sess_revision").val(),r=e("#import_option").val();a.LoadingOverlay("show"),e.post("api/var/var_import_collection",{sess_name:t,sess_revision:n,import_option:r},function(e){a.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):(a.modal("hide"),location.reload())})}()}),e("#start_variable_import_session").click(function(a){!function(){let a=e("#variable_import_modal"),t=e("#variable_import_sess_name").val(),n=e("#variable_import_sess_revision").val();e("#import_option").val(),a.LoadingOverlay("show"),e.post("api/var/start_import_session",{sess_name:t,sess_revision:n},function(e){a.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):window.location.href=base_url+"variable_import/"+e.session_id})}()}),e(".select-all-button").on("click",function(a){e(this).hasClass("btn-secondary")?t.rows({page:"current"}).select():t.rows({page:"current"}).deselect(),e(".select-all-button").toggleClass("btn-secondary btn-primary")}),t.on("user-select",function(){let a=e(".select-all-button");a.removeClass("btn-primary"),a.addClass("btn-secondary ")}),e("#multi-change-type-input").autocomplete({minLength:0,source:a,delay:100}).on("focus",function(){e(this).keydown()}).val(""),e(".apply-multi-edit").click(function(){i(t)}),e(".delete_button").confirmation({rootSelector:".delete_button"}).click(function(){i(t,del=!0)}),e("#add_constraint").click(function(){!function(){let a=e(".modal-content");a.LoadingOverlay("show");const t=e("#variable_name").val();parseInt(e("#modal_associated_row_index").val()),e.post("api/var/new_constraint",{name:t},function(t){a.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):e("#formalization_accordion").html(t.html)}).done(function(){l(),s(),c()})}()}),e("#save_new_enum_modal").click(function(){!function(){const a=e("#enum_name").val();e.post("api/var/add_new_enum",{name:a},function(e){!1===e.success?alert(e.errormsg):location.reload()})}()}),e("#add_enumerator").click(function(){_("")})})}).call(this,t(3))}});