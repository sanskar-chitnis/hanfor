!function(e){function t(t){for(var n,l,c=t[0],i=t[1],s=t[2],u=0,g=[];u<c.length;u++)l=c[u],r[l]&&g.push(r[l][0]),r[l]=0;for(n in i)Object.prototype.hasOwnProperty.call(i,n)&&(e[n]=i[n]);for(d&&d(t);g.length;)g.shift()();return o.push.apply(o,s||[]),a()}function a(){for(var e,t=0;t<o.length;t++){for(var a=o[t],n=!0,c=1;c<a.length;c++){var i=a[c];0!==r[i]&&(n=!1)}n&&(o.splice(t--,1),e=l(l.s=a[0]))}return e}var n={},r={1:0},o=[];function l(t){if(n[t])return n[t].exports;var a=n[t]={i:t,l:!1,exports:{}};return e[t].call(a.exports,a,a.exports,l),a.l=!0,a.exports}l.m=e,l.c=n,l.d=function(e,t,a){l.o(e,t)||Object.defineProperty(e,t,{enumerable:!0,get:a})},l.r=function(e){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},l.t=function(e,t){if(1&t&&(e=l(e)),8&t)return e;if(4&t&&"object"==typeof e&&e&&e.__esModule)return e;var a=Object.create(null);if(l.r(a),Object.defineProperty(a,"default",{enumerable:!0,value:e}),2&t&&"string"!=typeof e)for(var n in e)l.d(a,n,function(t){return e[t]}.bind(null,n));return a},l.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return l.d(t,"a",t),t},l.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)},l.p="";var c=window.webpackJsonp=window.webpackJsonp||[],i=c.push.bind(c);c.push=t,c=c.slice();for(var s=0;s<c.length;s++)t(c[s]);var d=i;o.push([158,0]),a()}({158:function(e,t,a){(function(e){a(19),a(10),a(17),a(16),a(15),a(14);const t=a(152);let n=sessionStorage.getItem("tag_search_string");function r(t){let a=e(".modal-content");a.LoadingOverlay("show");let n=e("#tag_name").val(),r=e("#occurences").val();e.post("api/tag/del_tag",{name:n,occurences:r},function(t){a.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):t.rebuild_table?location.reload():(tags_datatable.row(associated_row_id).data(t.data).draw(),e("#tag_modal").modal("hide"))})}e(document).ready(function(){let a=e("#tags_table"),o=a.DataTable({paging:!0,stateSave:!0,pageLength:50,responsive:!0,lengthMenu:[[10,50,100,500,-1],[10,50,100,500,"All"]],dom:'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',ajax:"api/tag/gets",deferRender:!0,columns:[{data:"name",render:function(e,t,a,n){return result='<a class="modal-opener" href="#">'+e+"</span></br>",result}},{data:"description",render:function(e,t,a,n){return result=e,result}},{data:"used_by",render:function(t,a,n,r){return result="",e(t).each(function(e,t){t.length>0&&(search_query="?command=search&col=2&q=%5C%22"+t+"%5C%22",result+='<span class="badge" style="background-color: '+n.color+'"><a href="'+base_url+search_query+'" target="_blank">'+t+"</a></span>")}),result}},{data:"used_by",visible:!1,searchable:!1,render:function(t,a,n,r){return result="",e(t).each(function(e,t){t.length>0&&(result.length>1&&(result+=", "),result+=t)}),result}}],initComplete:function(){e("#search_bar").val(n)}});o.column(3).visible(!1),e("#search_bar").keyup(function(){o.search(e(this).val()).draw(),sessionStorage.setItem("tag_search_string",e(this).val())}),a.find("tbody").on("click","a.modal-opener",function(t){t.preventDefault();let a=o.row(e(t.target).parent()).data(),n=o.row(e(t.target).parent()).index(),r=e(".modal-content");e("#tag_modal").modal("show"),e("#modal_associated_row_index").val(n),e("#tag_name_old").val(a.name),e("#occurences").val(a.used_by),e("#tag_modal_title").html("Tag: "+a.name),e("#tag_name").val(a.name),e("#tag_color").val(a.color),e("#tag-description").val(a.description),r.LoadingOverlay("hide")}),e("#save_tag_modal").click(function(){!function(t){let a=e(".modal-content");a.LoadingOverlay("show");let n=e("#tag_name").val(),r=e("#tag_name_old").val(),o=e("#occurences").val(),l=e("#tag_color").val(),c=parseInt(e("#modal_associated_row_index").val()),i=e("#tag-description").val();e.post("api/tag/update",{name:n,name_old:r,occurences:o,color:l,description:i},function(n){a.LoadingOverlay("hide",!0),!1===n.success?alert(n.errormsg):n.rebuild_table?location.reload():(t.row(c).data(n.data).draw(),e("#tag_modal").modal("hide"))})}(o)}),e(".delete_tag").confirmation({rootSelector:".delete_tag"}).click(function(){r(e(this).attr("name"))}),t(e("#tag-description"))})}).call(this,a(3))}});